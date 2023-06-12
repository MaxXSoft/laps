use regex_syntax::hir::{Class, Hir, HirKind, Literal, Repetition};
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::hash::Hash;
use std::iter::{once, repeat};
use std::str::from_utf8;

/// Mid-level intermediate representation of regular expressions
/// with symbol type `S` and tag type `T`.
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Mir<S, T> {
  /// The empty regular expression.
  Empty,
  /// A range of symbols.
  ///
  /// The range is closed. That is, the start and end of the range
  /// are included in the range.
  Range(S, S),
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
  /// Creates a new MIR from the given [`HirKind`].
  fn new_from_hir_kind(kind: HirKind) -> Result<Self, Error>
  where
    Self: MirHelper,
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
    Self: MirHelper,
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
  S: Hash + Eq + Clone,
  T: Hash + Eq + Clone,
{
  /// Optimizes the current MIR into a new one.
  pub fn optimize(self) -> Result<Self, Error> {
    // TODO: split symbol ranges
    match self {
      Self::Concat(c) => Self::optimize_concat(c),
      Self::Alter(a) => Self::optimize_alter(a),
      Self::Kleene(k) => Self::optimize_kleene(k),
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
        match Self::optimize(e)? {
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
      match Self::optimize(e)? {
        Self::Alter(a) => new_a
          .extend(a.into_iter().filter_map(|(e, inner_t)| {
            set.insert(e.clone()).then_some((e, t.clone().or(inner_t)))
          })),
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
    if new_a.iter().all(|(e, _)| matches!(e, Self::Concat(_))) {
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
            es.reverse();
            (Self::Concat(es), t)
          })
          .collect(),
      );
      // create concatenation
      return Ok(if same_subs.is_empty() {
        alter
      } else {
        same_subs.push(Self::optimize(alter)?);
        Self::Concat(same_subs)
      });
    }
    Ok(Self::Alter(new_a))
  }

  /// Optimized the given kleene closure.
  fn optimize_kleene(k: Box<Self>) -> Result<Self, Error> {
    let k = Self::optimize(*k)?;
    Ok(match k {
      // empty kleene closure is just an empty expression
      Self::Empty => Self::Empty,
      k => Self::Kleene(Box::new(k)),
    })
  }
}

macro_rules! impl_mir {
  ($ty:ty) => {
    impl<T> Mir<$ty, T> {
      /// Creates a new MIR from the given [`Hir`].
      pub fn new(hir: Hir) -> Result<Self, Error> {
        MirHelper::new(hir)
      }
    }

    impl<T> TryFrom<Hir> for Mir<$ty, T> {
      type Error = Error;

      fn try_from(hir: Hir) -> Result<Self, Self::Error> {
        Self::new(hir)
      }
    }
  };
}

impl_mir!(char);
impl_mir!(u8);

trait MirHelper: Sized {
  /// Creates a new MIR from the given [`Hir`].
  fn new(hir: Hir) -> Result<Self, Error>;

  /// Creates a new MIR from the given [`Literal`].
  fn new_from_literal(l: Literal) -> Result<Self, Error>;

  /// Creates a new MIR from the given [`Class`].
  fn new_from_class(c: Class) -> Result<Self, Error>;
}

impl<T> MirHelper for Mir<char, T> {
  fn new(hir: Hir) -> Result<Self, Error> {
    assert!(
      hir.properties().is_utf8(),
      "expected regex that matching UTF-8 characters"
    );
    Self::new_from_hir_kind(hir.into_kind())
  }

  fn new_from_literal(Literal(bs): Literal) -> Result<Self, Error> {
    from_utf8(&bs)
      .map(|s| Self::Concat(s.chars().map(|c| Self::Range(c, c)).collect()))
      .map_err(|_| Error::InvalidUtf8)
  }

  fn new_from_class(c: Class) -> Result<Self, Error> {
    match c {
      Class::Bytes(b) => Ok(Self::Alter(
        b.ranges()
          .iter()
          .map(|r| (Self::Range(r.start() as char, r.end() as char), None))
          .collect(),
      )),
      Class::Unicode(u) => Ok(Self::Alter(
        u.ranges()
          .iter()
          .map(|r| (Self::Range(r.start(), r.end()), None))
          .collect(),
      )),
    }
  }
}

impl<T> MirHelper for Mir<u8, T> {
  fn new(hir: Hir) -> Result<Self, Error> {
    assert!(
      !hir.properties().is_utf8(),
      "expected regex that matching bytes"
    );
    Self::new_from_hir_kind(hir.into_kind())
  }

  fn new_from_literal(Literal(bs): Literal) -> Result<Self, Error> {
    Ok(Self::Concat(
      bs.into_iter().map(|b| Self::Range(*b, *b)).collect(),
    ))
  }

  fn new_from_class(c: Class) -> Result<Self, Error> {
    match c {
      Class::Bytes(b) => Ok(Self::Alter(
        b.ranges()
          .iter()
          .map(|r| (Self::Range(r.start(), r.end()), None))
          .collect(),
      )),
      Class::Unicode(_) => Err(Error::UnsupportedOp("Unicode in byte mode")),
    }
  }
}

/// Possible errors during the creation of the [`Mir`].
#[derive(Debug)]
pub enum Error {
  InvalidUtf8,
  UnsupportedOp(&'static str),
  MatchesNothing,
}

impl fmt::Display for Error {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Self::InvalidUtf8 => write!(f, "invalid UTF-8 string in regex"),
      Self::UnsupportedOp(e) => write!(f, "{e} is not supported"),
      Self::MatchesNothing => write!(f, "the regex matches nothing"),
    }
  }
}
