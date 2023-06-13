pub mod dfa;
pub mod fa;
pub mod mir;
pub mod nfa;
pub mod table;

use regex_syntax::parse;
use std::io::{stdin, stdout, Write};
use std::num::NonZeroUsize;

type Mir = mir::Mir<char, NonZeroUsize>;

fn generate(res: &[&str]) -> Mir {
  Mir::Alter(
    res
      .iter()
      .enumerate()
      .map(|(i, re)| {
        (
          Mir::new(parse(re).unwrap()).unwrap(),
          NonZeroUsize::new(i + 1),
        )
      })
      .collect(),
  )
  .optimize()
  .unwrap()
}

fn main() {
  let mir = generate(&["if|else|while|at", "[_a-zA-Z][_a-zA-Z0-9]*"]);
  let nfa = nfa::NFA::new(mir);
  let dfa = dfa::DFA::new(nfa);
  let table = table::StateTransTable::new(dfa);
  'outer: loop {
    let mut id = table.init_id();
    print!("> ");
    stdout().flush().unwrap();
    let mut line = String::new();
    stdin().read_line(&mut line).unwrap();
    line.pop();
    for c in line.chars() {
      if let Some(next) = table.next_state(id, &c) {
        id = next;
      } else {
        println!("unmatched");
        continue 'outer;
      }
    }
    if let Some(tag) = table.is_final(id) {
      println!("matched ({tag}), id = {id}");
    } else {
      println!("unmatched");
    }
  }
}
