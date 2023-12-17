//! Mid-level intermediate representation ([`Mir`]) of regular expressions.
//!
//! A [`Mir`] can be built from the high-level intermediate representation
//! ([`regex_syntax::hir::Hir`]).

use regex_syntax::hir::{Class, Hir, HirKind, Literal, Repetition};
use std::collections::{BTreeMap, HashMap, HashSet};
use std::hash::Hash;
use std::iter::{once, repeat};
use std::str::from_utf8;
use std::{fmt, mem};

/// Mid-level intermediate representation of regular expressions
/// with symbol type `S` and tag type `T`.
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Mir<S, T> {
  /// The empty regular expression.
  Empty,
  /// Ranges of symbols, the ranges list can not be empty.
  ///
  /// All ranges are closed. That is, the start and end of the range
  /// are included in the range.
  Ranges(Vec<(S, S)>),
  /// A concatenation of expressions.
  Concat(Vec<Self>),
  /// An alternation of expressions and their tags.
  ///
  /// An alternation matches only if at least one of its sub-expressions match.
  /// If multiple sub-expressions match, then the leftmost is preferred.
  Alter(Vec<(Self, Option<T>)>),
  /// A kleene closure of an expression.
  Kleene(Box<Self>),
}

impl<S, T> Mir<S, T> {
  /// Creates a new MIR from the given [`Hir`].
  pub fn new(hir: Hir) -> Result<Self, Error>
  where
    Self: MirBuilder,
  {
    Self::new_from_hir_kind(hir.into_kind())
  }

  /// Creates a new MIR from the given [`HirKind`].
  fn new_from_hir_kind(kind: HirKind) -> Result<Self, Error>
  where
    Self: MirBuilder,
  {
    match kind {
      HirKind::Empty => Ok(Self::Empty),
      HirKind::Literal(l) => Self::new_from_literal(l),
      HirKind::Class(c) => Self::new_from_class(c),
      HirKind::Look(_) => Err(Error::UnsupportedOp("look-around assertion")),
      HirKind::Repetition(r) if !r.greedy => Err(Error::UnsupportedOp("non-greedy matching")),
      HirKind::Repetition(Repetition { min, max, sub, .. }) if min != 0 => {
        let rep1 = Self::new_n_repeats(*sub.clone(), min as usize)?;
        let rep2 = Self::new_from_hir_kind(HirKind::Repetition(Repetition {
          min: 0,
          max: max.map(|m| m - min),
          greedy: true,
          sub,
        }))?;
        Ok(Self::Concat(vec![rep1, rep2]))
      }
      HirKind::Repetition(Repetition {
        max: Some(max),
        sub,
        ..
      }) => once(Ok(Self::Empty))
        .chain((1..=max as usize).map(|n| Self::new_n_repeats(*sub.clone(), n)))
        .map(|r| r.map(|e| (e, None)))
        .collect::<Result<_, _>>()
        .map(Self::Alter),
      HirKind::Repetition(Repetition { max: None, sub, .. }) => {
        Self::new(*sub).map(|e| Self::Kleene(Box::new(e)))
      }
      HirKind::Capture(c) => Self::new(*c.sub),
      HirKind::Concat(c) => c
        .into_iter()
        .map(Self::new)
        .collect::<Result<_, _>>()
        .map(Self::Concat),
      HirKind::Alternation(a) => a
        .into_iter()
        .map(|hir| Self::new(hir).map(|e| (e, None)))
        .collect::<Result<_, _>>()
        .map(Self::Alter),
    }
  }

  /// Creates a new MIR which matches `n` repeats of the given [`Hir`].
  fn new_n_repeats(hir: Hir, n: usize) -> Result<Self, Error>
  where
    Self: MirBuilder,
  {
    repeat(hir)
      .take(n)
      .map(Self::new)
      .collect::<Result<_, _>>()
      .map(Self::Concat)
  }
}

impl<S, T> Mir<S, T>
where
  S: Hash + Eq + Clone + Ord + SymbolOp,
  T: Hash + Eq + Clone,
{
  /// Optimizes the current MIR into a new one.
  pub fn optimize(mut self) -> Result<Self, Error> {
    self.normalize_ranges()?;
    let symbols = self.symbol_set();
    let (syms, lmap, rmap) = Self::into_triple(symbols);
    self.rebuild(&syms, &lmap, &rmap).opt_without_rebuild()
  }

  /// Normalizes all ranges in [`Ranges`](Mir::Ranges).
  ///
  /// Returns error if empty range exists.
  fn normalize_ranges(&mut self) -> Result<(), Error> {
    match self {
      Self::Empty => Ok(()),
      Self::Ranges(rs) if rs.is_empty() => Err(Error::MatchesNothing),
      Self::Ranges(rs) => {
        rs.sort_unstable();
        let new_rs = mem::take(rs);
        *rs = new_rs.into_iter().fold(Vec::new(), |mut rs, (cl, cr)| {
          match rs.last_mut() {
            Some((_, lr)) if &cr <= lr => {}
            Some((_, lr)) if cl.prev().as_ref() <= Some(lr) => *lr = cr,
            _ => rs.push((cl, cr)),
          }
          rs
        });
        Ok(())
      }
      Self::Concat(c) => {
        for e in c {
          e.normalize_ranges()?;
        }
        Ok(())
      }
      Self::Alter(a) => {
        for (e, _) in a {
          e.normalize_ranges()?;
        }
        Ok(())
      }
      Self::Kleene(k) => k.normalize_ranges(),
    }
  }

  /// Returns the symbol set of the current MIR.
  fn symbol_set(&self) -> BTreeMap<S, (S, Vec<(S, S)>)> {
    // collect symbols
    let mut symbols: Vec<_> = self.collect_symbols().into_iter().collect();
    // divide ranges
    let mut ranges = BTreeMap::new();
    while let Some(cur_rs) = symbols.pop() {
      let (left, right) = Self::endpoints_of(&cur_rs);
      // find left endpoint in range map
      match ranges.range_mut(..=left).next_back() {
        None => {}
        Some((_, (r, _))) if &*r < left => {}
        Some((l, (r, rs))) if l < left || /* l == left && */ &*r > right => {
          // divide `rs`
          let (lefts, rights) = if l < left {
            Self::split_ranges(mem::take(rs), left)
          } else {
            Self::split_ranges(mem::take(rs), &right.next().unwrap())
          };
          *r = Self::endpoints_of(&lefts).1.clone();
          *rs = lefts;
          let (l, r) = Self::endpoints_of(&rights);
          ranges.insert(l.clone(), (r.clone(), rights));
          // push `cur_rs` to the worklist
          symbols.push(cur_rs);
          continue;
        }
        Some((_, (r, rs))) if /* l == left && */ r == right && rs != &cur_rs => {
          // left and right endpoint found in range map, but the ranges
          // are different, so divide `rs` into individual ranges
          let mut iter = mem::take(rs).into_iter();
          let first = iter.next().unwrap();
          *r = first.1.clone();
          *rs = vec![first];
          ranges.extend(iter.map(|r| (r.0.clone(), (r.1.clone(), vec![r]))));
          // push all the ranges of `cur_rs` to the worklist
          symbols.extend(cur_rs.into_iter().map(|r| vec![r]));
          continue;
        }
        Some((_, (r, _))) if /* l == left && */ r == right => continue,
        Some((_, (r, _))) if /* l == left && */ &*r < right => {
          // divide `cur_rs`
          let (lefts, rights) = Self::split_ranges(cur_rs, &r.next().unwrap());
          // push the divided ranges to the worklist
          symbols.push(lefts);
          if !rights.is_empty() {
            symbols.push(rights);
          }
          continue;
        }
        _ => unreachable!(),
      }
      // find right endpoint in range map
      match ranges.range(..=right).next_back() {
        None => {}
        Some((_, (r, _))) if r < left => {}
        Some((l, _)) => {
          // divide `cur_rs`
          let left = left.clone();
          let (lefts, rights) = Self::split_ranges(cur_rs, l);
          // insert the left part to range map, and the right to worklist
          ranges.insert(left, (Self::endpoints_of(&lefts).1.clone(), lefts));
          symbols.push(rights);
          continue;
        }
      }
      // just insert to range map
      ranges.insert(left.clone(), (right.clone(), cur_rs));
    }
    ranges
  }

  /// Returns the [`SymbolSetTriple`] of the given symbol set.
  fn into_triple(symbols: BTreeMap<S, (S, Vec<(S, S)>)>) -> SymbolSetTriple<S> {
    let (syms, (lmap, rmap)) = symbols
      .into_iter()
      .enumerate()
      .map(|(i, (l, (r, rs)))| (rs, ((l, i), (r, i))))
      .unzip();
    (syms, lmap, rmap)
  }

  /// Collects all symbols in the current MIR.
  fn collect_symbols(&self) -> HashSet<Vec<(S, S)>> {
    match self {
      Self::Empty => HashSet::new(),
      Self::Ranges(rs) => [rs.clone()].into(),
      Self::Concat(c) => c.iter().flat_map(|e| e.collect_symbols()).collect(),
      Self::Alter(a) => a.iter().flat_map(|(e, _)| e.collect_symbols()).collect(),
      Self::Kleene(k) => k.collect_symbols(),
    }
  }

  /// Returns the left and right endpoint of the given ranges.
  fn endpoints_of(ranges: &[(S, S)]) -> (&S, &S) {
    (&ranges.first().unwrap().0, &ranges.last().unwrap().1)
  }

  /// Splits the given ranges at the given point.
  ///
  /// Returns ranges `[..at]` and `[at..]` (may be empty).
  fn split_ranges(mut ranges: Vec<(S, S)>, at: &S) -> (Vec<(S, S)>, Vec<(S, S)>) {
    let right = match ranges.binary_search_by_key(&at, |(l, _)| l) {
      Ok(i) => ranges.drain(i..).collect(),
      Err(0) => mem::take(&mut ranges),
      Err(i) => {
        let (_, r) = ranges.get_mut(i - 1).unwrap();
        if at > r {
          ranges.drain(i..).collect()
        } else {
          let last_r = r.clone();
          *r = at.prev().unwrap();
          let mut right = vec![(at.clone(), last_r)];
          right.extend(ranges.drain(i..));
          right
        }
      }
    };
    (ranges, right)
  }

  /// Rebuilds the current MIR by the given symbol set and mappings.
  fn rebuild(
    self,
    syms: &[Vec<(S, S)>],
    lmap: &HashMap<S, usize>,
    rmap: &HashMap<S, usize>,
  ) -> Self {
    match self {
      Self::Empty => self,
      Self::Ranges(rs) => {
        let (l, r) = Self::endpoints_of(&rs);
        Self::Alter(
          (lmap[l]..=rmap[r])
            .map(|i| (Self::Ranges(syms[i].clone()), None))
            .collect(),
        )
      }
      Self::Concat(c) => Self::Concat(c.into_iter().map(|e| e.rebuild(syms, lmap, rmap)).collect()),
      Self::Alter(a) => Self::Alter(
        a.into_iter()
          .map(|(e, t)| (e.rebuild(syms, lmap, rmap), t))
          .collect(),
      ),
      Self::Kleene(k) => Self::Kleene(Box::new(k.rebuild(syms, lmap, rmap))),
    }
  }

  /// Optimizes the current MIR into a new one.
  ///
  /// This method will not rebuild the MIR.
  fn opt_without_rebuild(self) -> Result<Self, Error> {
    match self {
      Self::Concat(c) => Self::optimize_concat(c),
      Self::Alter(a) => Self::optimize_alter(a),
      Self::Kleene(k) => Self::optimize_kleene(*k),
      e => Ok(e),
    }
  }

  /// Optimized the given concatenation.
  fn optimize_concat(c: Vec<Self>) -> Result<Self, Error> {
    if c.is_empty() {
      Err(Error::MatchesNothing)
    } else {
      // optimize all sub-expressions, flatten nested concatenations
      // and remove empty expressions
      let mut new_c = Vec::new();
      for e in c {
        match e.opt_without_rebuild()? {
          Self::Empty => {}
          Self::Concat(c) => new_c.extend(c),
          e => new_c.push(e),
        }
      }
      // check length
      Ok(match new_c.len() {
        0 => Self::Empty,
        1 => new_c.swap_remove(0),
        _ => Self::Concat(new_c),
      })
    }
  }

  /// Optimized the given alternation.
  fn optimize_alter(a: Vec<(Self, Option<T>)>) -> Result<Self, Error> {
    if a.is_empty() {
      return Err(Error::MatchesNothing);
    }
    // collect expressions that have a tag
    let tagged_exps: HashMap<_, _> = a
      .iter()
      .filter_map(|(e, t)| t.clone().map(|t| (e.clone(), t)))
      .collect();
    // optimize all sub-expressions, flatten nested alternations
    // and remove duplicate expressions
    let mut new_a = Vec::new();
    let mut set = HashSet::new();
    for (e, _) in a {
      // get the tag of the current expresson
      let t = tagged_exps.get(&e).cloned();
      // optimize, and handle by kind
      match e.opt_without_rebuild()? {
        Self::Alter(a) => new_a.extend(
          a.into_iter()
            .filter_map(|(e, inner_t)| set.insert(e.clone()).then(|| (e, t.clone().or(inner_t)))),
        ),
        e => {
          if set.insert(e.clone()) {
            new_a.push((e, t));
          }
        }
      }
    }
    // return if the alternation has only one untagged sub-expression
    if new_a.len() == 1 {
      if let Some((e, None)) = new_a.first() {
        return Ok(e.clone());
      }
    }
    // optimize alternation of concatenations
    if new_a.len() > 1 && new_a.iter().all(|(e, _)| matches!(e, Self::Concat(_))) {
      // extract reversed sub-expressions in concatenations
      let mut rev_subs: Vec<(Vec<_>, _)> = new_a
        .into_iter()
        .map(|(e, t)| match e {
          Self::Concat(mut c) => {
            c.reverse();
            (c, t)
          }
          _ => unreachable!(),
        })
        .collect();
      // extract the first n same expressions in sub-expressions
      let mut same_subs = Vec::new();
      loop {
        // check if all the last expressions are same
        let mut iter = rev_subs.iter().map(|(es, _)| es.last());
        let first = iter.next().unwrap();
        if first.is_none() {
          break;
        }
        if !iter.all(|e| e == first) {
          break;
        }
        // add to `same_subs`, and pop the last expression
        same_subs.push(first.unwrap().clone());
        rev_subs.iter_mut().for_each(|(es, _)| {
          es.pop();
        });
      }
      // create alternation
      let alter = Self::Alter(
        rev_subs
          .into_iter()
          .map(|(mut es, t)| {
            if es.is_empty() {
              (Self::Empty, t)
            } else {
              es.reverse();
              (Self::Concat(es), t)
            }
          })
          .collect(),
      );
      // create concatenation
      return Ok(if same_subs.is_empty() {
        alter
      } else {
        same_subs.push(alter.opt_without_rebuild()?);
        Self::Concat(same_subs)
      });
    }
    Ok(Self::Alter(new_a))
  }

  /// Optimized the given kleene closure.
  fn optimize_kleene(k: Self) -> Result<Self, Error> {
    Ok(match k.opt_without_rebuild()? {
      // empty kleene closure is just an empty expression
      Self::Empty => Self::Empty,
      k => Self::Kleene(Box::new(k)),
    })
  }
}

impl<S, T> TryFrom<Hir> for Mir<S, T>
where
  Self: MirBuilder,
{
  type Error = Error;

  fn try_from(hir: Hir) -> Result<Self, Self::Error> {
    Self::new(hir)
  }
}

/// Helper trait for building MIRs with some specific symbol types.
pub trait MirBuilder: Sized {
  /// Creates a new MIR from the given [`Literal`].
  fn new_from_literal(l: Literal) -> Result<Self, Error>;

  /// Creates a new MIR from the given [`Class`].
  fn new_from_class(c: Class) -> Result<Self, Error>;
}

impl<T> MirBuilder for Mir<char, T> {
  fn new_from_literal(Literal(bs): Literal) -> Result<Self, Error> {
    from_utf8(&bs)
      .map(|s| Self::Concat(s.chars().map(|c| Self::Ranges(vec![(c, c)])).collect()))
      .map_err(|_| Error::InvalidUtf8)
  }

  fn new_from_class(c: Class) -> Result<Self, Error> {
    match c {
      Class::Bytes(b) => Ok(Self::Ranges(
        b.ranges()
          .iter()
          .map(|r| (r.start() as char, r.end() as char))
          .collect(),
      )),
      Class::Unicode(u) => Ok(Self::Ranges(
        u.ranges().iter().map(|r| (r.start(), r.end())).collect(),
      )),
    }
  }
}

impl<T> MirBuilder for Mir<u8, T> {
  fn new_from_literal(Literal(bs): Literal) -> Result<Self, Error> {
    Ok(Self::Concat(
      bs.iter().map(|b| Self::Ranges(vec![(*b, *b)])).collect(),
    ))
  }

  fn new_from_class(c: Class) -> Result<Self, Error> {
    match c {
      Class::Bytes(b) => Ok(Self::Ranges(
        b.ranges().iter().map(|r| (r.start(), r.end())).collect(),
      )),
      Class::Unicode(_) => Err(Error::UnsupportedOp("Unicode in byte mode")),
    }
  }
}

/// Possible errors during the creation of the [`Mir`].
#[derive(Debug)]
pub enum Error {
  /// There is a invalid UTF-8 string regular expression.
  InvalidUtf8,
  /// Regular expression contains unsupported operations.
  UnsupportedOp(&'static str),
  /// Regular expression matches nothing.
  MatchesNothing,
  /// Failed to build the symbol set of regular expressions.
  FailedToBuildSymbolSet,
}

impl fmt::Display for Error {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Self::InvalidUtf8 => write!(f, "invalid UTF-8 string in regex"),
      Self::UnsupportedOp(e) => write!(f, "{e} is not supported"),
      Self::MatchesNothing => write!(f, "the regex matches nothing"),
      Self::FailedToBuildSymbolSet => write!(f, "failed to build the symbol set"),
    }
  }
}

/// A triple of symbol set, left bound index map and right bound index map.
type SymbolSetTriple<S> = (Vec<Vec<(S, S)>>, HashMap<S, usize>, HashMap<S, usize>);

/// Trait for getting the previous or next symbol of a given symbol.
pub trait SymbolOp: Sized {
  /// Returns the previous symbol of the current symbol.
  ///
  /// Returns [`None`] if there is no previous symbol of the current symbol.
  fn prev(&self) -> Option<Self>;

  /// Returns the next symbol of the current symbol.
  ///
  /// Returns [`None`] if there is no next symbol of the current symbol.
  fn next(&self) -> Option<Self>;
}

impl SymbolOp for char {
  fn prev(&self) -> Option<Self> {
    match self {
      '\0' => None,
      '\u{e000}' => Some('\u{d7ff}'),
      _ => Some(unsafe { char::from_u32_unchecked(*self as u32 - 1) }),
    }
  }

  fn next(&self) -> Option<Self> {
    match self {
      '\u{d7ff}' => Some('\u{e000}'),
      '\u{10fff}' => None,
      _ => Some(unsafe { char::from_u32_unchecked(*self as u32 + 1) }),
    }
  }
}

impl SymbolOp for u8 {
  fn prev(&self) -> Option<Self> {
    (*self != u8::MIN).then_some(self - 1)
  }

  fn next(&self) -> Option<Self> {
    (*self != u8::MAX).then_some(self + 1)
  }
}
