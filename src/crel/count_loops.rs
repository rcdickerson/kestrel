use crate::crel::ast::*;

pub struct LoopCounts {
  pub num_loops: usize,
  pub num_merged: usize,
  pub num_runoffs: usize,
}

impl LoopCounts {
  pub fn zero() -> Self {
    LoopCounts { num_loops: 0, num_merged: 0, num_runoffs: 0 }
  }

  pub fn plus(&self, other: &LoopCounts) -> Self {
    LoopCounts {
      num_loops: self.num_loops + other.num_loops,
      num_merged: self.num_merged + other.num_merged,
      num_runoffs: self.num_runoffs + other.num_runoffs,
    }
  }
}

impl std::iter::Sum for LoopCounts {
  fn sum<I>(iter: I) -> Self
    where I: Iterator<Item = LoopCounts>
  {
    let mut num_loops = 0;
    let mut num_merged = 0;
    let mut num_runoffs = 0;
    for count in iter {
      num_loops += count.num_loops;
      num_merged += count.num_merged;
      num_runoffs += count.num_runoffs;
    }
    LoopCounts { num_loops, num_merged, num_runoffs }
  }
}

pub trait CountLoops {
  fn count_loops(&self) -> LoopCounts;
}

impl CountLoops for CRel {
  fn count_loops(&self) -> LoopCounts {
    match self {
      CRel::Declaration(_) => LoopCounts::zero(),
      CRel::FunctionDefinition{specifiers:_, name:_, params:_, body} => {
        body.count_loops()
      },
      CRel::Seq(crels) => crels.iter().map(|c| c.count_loops()).sum(),
    }
  }
}

impl CountLoops for Expression {
  fn count_loops(&self) -> LoopCounts {
    match self {
      Expression::Identifier{..}      => LoopCounts::zero(),
      Expression::ConstBool(_)        => LoopCounts::zero(),
      Expression::ConstInt(_)         => LoopCounts::zero(),
      Expression::ConstFloat(_)       => LoopCounts::zero(),
      Expression::StringLiteral(_)    => LoopCounts::zero(),
      Expression::Call{..}            => LoopCounts::zero(),
      Expression::Unop{expr, ..}      => expr.count_loops(),
      Expression::Binop{lhs, rhs, ..} => lhs.count_loops().plus(&rhs.count_loops()),
      Expression::Forall{..}          => LoopCounts::zero(),
      Expression::SketchHole          => LoopCounts::zero(),
      Expression::Statement(stmt)     => stmt.count_loops(),
      Expression::Ternary{ then, els, .. }  => {
        then.count_loops().plus(&els.count_loops())
      }
    }
  }
}

impl CountLoops for Statement {
  fn count_loops(&self) -> LoopCounts {
    match self {
      Statement::Assert(_) => LoopCounts::zero(),
      Statement::Assume(_) => LoopCounts::zero(),
      Statement::BasicBlock(items) => items.iter().map(|i| i.count_loops()).sum(),
      Statement::Break => LoopCounts::zero(),
      Statement::Compound(items) => items.iter().map(|i| i.count_loops()).sum(),
      Statement::Expression(expr) => expr.count_loops(),
      Statement::GuardedRepeat{repetitions, body, ..} => {
        let counts = body.count_loops();
        LoopCounts {
          num_loops: repetitions * counts.num_loops,
          num_merged: repetitions * counts.num_merged,
          num_runoffs: repetitions * counts.num_runoffs,
        }
      }
      Statement::If{condition:_, then, els} => {
        let else_count = match els {
          None => LoopCounts::zero(),
          Some(stmt) => stmt.count_loops(),
        };
        then.count_loops().plus(&else_count)
      }
      Statement::None => LoopCounts::zero(),
      Statement::Relation{lhs, rhs} => {
        lhs.count_loops().plus(&rhs.count_loops())
      },
      Statement::Return(_) => LoopCounts::zero(),
      Statement::While{condition, body, is_runoff, is_merged, ..} => {
        let cond_loops = condition.count_loops();
        let body_loops = match body {
          None => LoopCounts::zero(),
          Some(body) => body.count_loops(),
        };
        LoopCounts {
          num_loops: cond_loops.num_loops + body_loops.num_loops + 1,
          num_merged: cond_loops.num_loops + body_loops.num_loops + (if *is_merged {1} else {0}),
          num_runoffs: cond_loops.num_runoffs + body_loops.num_runoffs + (if *is_runoff {1} else {0}),
        }
      },
    }
  }
}

impl CountLoops for Declaration {
  fn count_loops(&self) -> LoopCounts {
    match &self.initializer {
      None => LoopCounts::zero(),
      Some(expr) => expr.count_loops(),
    }
  }
}

impl CountLoops for DeclarationSpecifier {
  fn count_loops(&self) -> LoopCounts { LoopCounts::zero() }
}

impl CountLoops for Declarator {
  fn count_loops(&self) -> LoopCounts { LoopCounts::zero() }
}

impl CountLoops for Initializer {
  fn count_loops(&self) -> LoopCounts {
    match self {
      Initializer::Expression(expr) => expr.count_loops(),
      Initializer::List(exprs) => {
        let mut count = LoopCounts::zero();
        for expr in exprs {
          count = count.plus(&expr.count_loops());
        }
        count
      }
    }
  }
}

impl CountLoops for BlockItem {
  fn count_loops(&self) -> LoopCounts {
    match self {
      BlockItem::Declaration(decl) => decl.count_loops(),
      BlockItem::Statement(stmt) => stmt.count_loops(),
    }
  }
}
