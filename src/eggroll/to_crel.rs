//! Converts an [Eggroll] term to a corresponding [CRel] term.

use crate::crel::ast::*;
use sexp::{Atom, Sexp};
use std::collections::HashMap;
use uuid::Uuid;

#[derive(Debug, Clone)]
pub struct Config {
  pub assert_name: Option<String>,
  pub assume_name: Option<String>,
  pub nondet_name: Option<String>,
}

impl Config {
  pub fn default() -> Self {
    Config {
      assert_name: None,
      assume_name: None,
      nondet_name: None,
    }
  }
}

#[derive(Debug, Clone)]
pub struct GuardedRepetitions {
  guarded_reps: HashMap<String, usize>,
  pub loop_reps: HashMap<String, (usize, usize)>,
}

impl GuardedRepetitions {
  pub fn new() -> Self {
    GuardedRepetitions {
      guarded_reps: HashMap::new(),
      loop_reps: HashMap::new(),
    }
  }

  pub fn set_repetitions(&mut self, id: String, reps: usize) {
    self.guarded_reps.insert(id, reps);
  }

  pub fn set_loop_repetitions(&mut self, id: String, lhs_reps: usize, rhs_reps: usize) {
    self.loop_reps.insert(id, (lhs_reps, rhs_reps));
  }
}

struct Context<'a> {
  config: &'a Config,
  repetitions: &'a GuardedRepetitions,
}

pub fn eggroll_to_crel(eggroll: &String, config: &Config, repetitions: &GuardedRepetitions) -> CRel {
  match sexp::parse(eggroll.as_str()) {
    Err(msg) => panic!("{}", msg),
    Ok(sexp) => expect_crel(&sexp, &Context{config, repetitions}),
  }
}

fn expect_crel(sexp: &Sexp, ctx: &Context) -> CRel {
  match &sexp {
    Sexp::Atom(Atom::S(s)) if s.is_empty() => CRel::Seq(Vec::new()),
    Sexp::List(sexps) => match &sexps[0] {
      Sexp::Atom(Atom::S(s)) if s == "declaration" => {
        let declaration = expect_declaration(&sexps[1], ctx);
        CRel::Declaration(declaration)
      },
      Sexp::Atom(Atom::S(s)) if s == "fundef" => {
        let specifiers = expect_specifiers(&sexps[1]);
        let name = expect_string(&sexps[2]);
        let params = expect_param_decls(&sexps[3], ctx);
        let body = Box::new(expect_statement(&sexps[4], ctx));
        CRel::FunctionDefinition{specifiers, name, params, body}
      },
      Sexp::Atom(Atom::S(s)) if s == "seq" => {
        let mut seq = vec!(expect_crel(&sexps[1], ctx));
        let rhs = expect_crel(&sexps[2], ctx);
        match rhs {
          CRel::Seq(crels) => seq.append(&mut crels.to_owned()),
          _ => seq.push(rhs),
        };
        CRel::Seq(seq)
      },
      _ => panic!("Expected CRel s-expression, got: {}", sexp),
    },
    _ => panic!("Expected CRel s-expression, got: {}", sexp),
  }
}

fn expect_expression(sexp: &Sexp, ctx: &Context) -> Expression {
  match &sexp {
    Sexp::Atom(Atom::S(s)) if !s.is_empty() => Expression::Identifier{name: s.clone()},
    Sexp::List(sexps) => match &sexps[0] {
      Sexp::Atom(Atom::S(s)) if s == "lit-string" => {
        Expression::StringLiteral(expect_string(&sexps[1]))
      },
      Sexp::Atom(Atom::S(s)) if s == "const-int" => {
        match &sexps[1] {
          Sexp::Atom(Atom::I(i)) => Expression::ConstInt(i32::try_from(*i).unwrap()),
          _ => panic!("Cannot convert to integer from {:?}", sexps[1]),
        }
      },
      Sexp::Atom(Atom::S(s)) if s == "const-float" => {
        match &sexps[1] {
          Sexp::Atom(Atom::S(s)) => Expression::ConstFloat(s.parse().unwrap()),
          _ => panic!("Cannot convert to integer from {:?}", sexps[1]),
        }
      },
      Sexp::Atom(Atom::S(s)) if s == "neg" => {
        let expr = Box::new(expect_expression(&sexps[1], ctx));
        Expression::Unop{ expr, op: UnaryOp::Minus }
      },
      Sexp::Atom(Atom::S(s)) if s == "not" => {
        let expr = Box::new(expect_expression(&sexps[1], ctx));
        Expression::Unop{ expr, op: UnaryOp::Not }
      },
      Sexp::Atom(Atom::S(s)) if s == "call" => {
        let callee = Box::new(expect_expression(&sexps[1], ctx));
        let args = expect_args(&sexps[2], ctx);
        Expression::Call{ callee, args }
      },
      Sexp::Atom(Atom::S(s)) if s == "a-spec-call" => {
        let callee = Box::new(expect_expression(&sexps[1], ctx));
        let args = expect_args(&sexps[2], ctx);
        Expression::ASpecCall{ callee, args }
      },
      Sexp::Atom(Atom::S(s)) if s == "e-spec-call" => {
        let callee = Box::new(expect_expression(&sexps[1], ctx));
        let args = expect_args(&sexps[2], ctx);
        Expression::ESpecCall{ callee, args }
      },
      Sexp::Atom(Atom::S(s)) if s == "index" => {
        let lhs = Box::new(expect_expression(&sexps[1], ctx));
        let rhs = Box::new(expect_expression(&sexps[2], ctx));
        Expression::Binop{ lhs, rhs, op: BinaryOp::Index }
      },
      Sexp::Atom(Atom::S(s)) if s == "forall" => {
        let bindings = expect_bindings(&sexps[1]);
        let condition = Box::new(expect_expression(&sexps[2], ctx));
        Expression::Forall{bindings, condition}
      },
      Sexp::Atom(Atom::S(s)) if s == "+" => {
        let lhs = Box::new(expect_expression(&sexps[1], ctx));
        let rhs = Box::new(expect_expression(&sexps[2], ctx));
        Expression::Binop{ lhs, rhs, op: BinaryOp::Add }
      },
      Sexp::Atom(Atom::S(s)) if s == "&&" => {
        let lhs = Box::new(expect_expression(&sexps[1], ctx));
        let rhs = Box::new(expect_expression(&sexps[2], ctx));
        Expression::Binop{ lhs, rhs, op: BinaryOp::And }
      },
      Sexp::Atom(Atom::S(s)) if s == "=" => {
        let lhs = Box::new(expect_expression(&sexps[1], ctx));
        let rhs = Box::new(expect_expression(&sexps[2], ctx));
        Expression::Binop{ lhs, rhs, op: BinaryOp::Assign }
      },
      Sexp::Atom(Atom::S(s)) if s == "-" => {
        let lhs = Box::new(expect_expression(&sexps[1], ctx));
        let rhs = Box::new(expect_expression(&sexps[2], ctx));
        Expression::Binop{ lhs, rhs, op: BinaryOp::Sub }
      },
      Sexp::Atom(Atom::S(s)) if s == "/" => {
        let lhs = Box::new(expect_expression(&sexps[1], ctx));
        let rhs = Box::new(expect_expression(&sexps[2], ctx));
        Expression::Binop{ lhs, rhs, op: BinaryOp::Div }
      },
      Sexp::Atom(Atom::S(s)) if s == "==" => {
        let lhs = Box::new(expect_expression(&sexps[1], ctx));
        let rhs = Box::new(expect_expression(&sexps[2], ctx));
        Expression::Binop{ lhs, rhs, op: BinaryOp::Equals }
      },
      Sexp::Atom(Atom::S(s)) if s == ">" => {
        let lhs = Box::new(expect_expression(&sexps[1], ctx));
        let rhs = Box::new(expect_expression(&sexps[2], ctx));
        Expression::Binop{ lhs, rhs, op: BinaryOp::Gt }
      },
      Sexp::Atom(Atom::S(s)) if s == ">=" => {
        let lhs = Box::new(expect_expression(&sexps[1], ctx));
        let rhs = Box::new(expect_expression(&sexps[2], ctx));
        Expression::Binop{ lhs, rhs, op: BinaryOp::Gte }
      },
      Sexp::Atom(Atom::S(s)) if s == "<" => {
        let lhs = Box::new(expect_expression(&sexps[1], ctx));
        let rhs = Box::new(expect_expression(&sexps[2], ctx));
        Expression::Binop{ lhs, rhs, op: BinaryOp::Lt }
      },
      Sexp::Atom(Atom::S(s)) if s == "<=" => {
        let lhs = Box::new(expect_expression(&sexps[1], ctx));
        let rhs = Box::new(expect_expression(&sexps[2], ctx));
        Expression::Binop{ lhs, rhs, op: BinaryOp::Lte }
      },
      Sexp::Atom(Atom::S(s)) if s == "mod" => {
        let lhs = Box::new(expect_expression(&sexps[1], ctx));
        let rhs = Box::new(expect_expression(&sexps[2], ctx));
        Expression::Binop{ lhs, rhs, op: BinaryOp::Mod }
      },
      Sexp::Atom(Atom::S(s)) if s == "*" => {
        let lhs = Box::new(expect_expression(&sexps[1], ctx));
        let rhs = Box::new(expect_expression(&sexps[2], ctx));
        Expression::Binop{ lhs, rhs, op: BinaryOp::Mul }
      },
      Sexp::Atom(Atom::S(s)) if s == "!=" => {
        let lhs = Box::new(expect_expression(&sexps[1], ctx));
        let rhs = Box::new(expect_expression(&sexps[2], ctx));
        Expression::Binop{ lhs, rhs, op: BinaryOp::NotEquals }
      },
      Sexp::Atom(Atom::S(s)) if s == "||" => {
        let lhs = Box::new(expect_expression(&sexps[1], ctx));
        let rhs = Box::new(expect_expression(&sexps[2], ctx));
        Expression::Binop{ lhs, rhs, op: BinaryOp::Or }
      },
      _ => Expression::Statement(Box::new(expect_statement(sexp, ctx))),
    },
    _ => Expression::Statement(Box::new(expect_statement(sexp, ctx))),
  }
}

fn expect_statement(sexp: &Sexp, ctx: &Context) -> Statement {
  match &sexp {
    Sexp::Atom(Atom::S(s)) if s == "break" => Statement::Break,
    Sexp::Atom(Atom::S(s)) if s == "fail" => Statement::Fail,
    Sexp::Atom(Atom::S(s)) if s == "skip" => Statement::Compound(vec![]),
    Sexp::Atom(Atom::S(s)) if s == "return-none" => Statement::Return(None),
    Sexp::List(sexps) => match &sexps[0] {
      Sexp::Atom(Atom::S(s)) if s == "basic-block" => {
        let items = sexps[1..].iter()
          .map(|x| expect_block_item(x, ctx))
          .collect::<Vec<_>>();
        Statement::BasicBlock(items)
      },
      Sexp::Atom(Atom::S(s)) if s == "seq" => {
        let mut seq = vec!(expect_block_item(&sexps[1], ctx));
        let rhs = expect_statement(&sexps[2], ctx);
        match rhs {
            Statement::Compound(items) => {
            seq.append(&mut items.to_owned())
          },
          _ => seq.push(BlockItem::Statement(rhs)),
        };
        Statement::Compound(seq)
      },
      Sexp::Atom(Atom::S(s)) if s == "if" => {
        let condition = Box::new(expect_expression(&sexps[1], ctx));
        let then = Box::new(expect_statement(&sexps[2], ctx));
        Statement::If{condition, then, els: None}
      },
      Sexp::Atom(Atom::S(s)) if s == "if-else" => {
        let condition = Box::new(expect_expression(&sexps[1], ctx));
        let then = Box::new(expect_statement(&sexps[2], ctx));
        let els  = Some(Box::new(expect_statement(&sexps[3], ctx)));
        Statement::If{condition, then, els}
      },
      Sexp::Atom(Atom::S(s)) if s == "if-rel" => {
        let cond1 = Box::new(expect_expression(&sexps[1], ctx));
        let cond2 = Box::new(expect_expression(&sexps[2], ctx));
        let then1 = expect_statement(&sexps[3], ctx);
        let then2 = expect_statement(&sexps[4], ctx);
        let els1  = expect_statement(&sexps[5], ctx);
        let els2  = expect_statement(&sexps[6], ctx);

        let cond_both = Box::new(Expression::Binop {
          lhs: cond1.clone(),
          rhs: cond2.clone(),
          op: BinaryOp::And
        });
        let cond_left_only = Box::new(Expression::Binop {
          lhs: cond1.clone(),
          rhs: Box::new(Expression::Unop {op: UnaryOp::Not, expr: cond2.clone()}),
          op: BinaryOp::And
        });
        let cond_right_only = Box::new(Expression::Binop {
          lhs: Box::new(Expression::Unop {op: UnaryOp::Not, expr: cond1.clone()}),
          rhs: cond2.clone(),
          op: BinaryOp::And
        });
        let cond_neither = Box::new(Expression::Binop {
          lhs: Box::new(Expression::Unop {op: UnaryOp::Not, expr: cond1.clone()}),
          rhs: cond2.clone(),
          op: BinaryOp::And
        });

        let then_then = Box::new(Statement::Compound(vec![
          BlockItem::Statement(then1.clone()),
          BlockItem::Statement(then2.clone())
        ]));
        let then_else = Box::new(Statement::Compound(vec![
          BlockItem::Statement(then1.clone()),
          BlockItem::Statement(els2.clone())
        ]));
        let else_then = Box::new(Statement::Compound(vec![
          BlockItem::Statement(els1.clone()),
          BlockItem::Statement(then2.clone())
        ]));
        let else_else = Box::new(Statement::Compound(vec![
          BlockItem::Statement(els1.clone()),
          BlockItem::Statement(els2.clone())
        ]));

        Statement::If {
          condition: cond_both,
          then: then_then,
          els: Some(Box::new(Statement::If {
            condition: cond_left_only,
            then: then_else,
            els: Some(Box::new(Statement::If {
              condition: cond_right_only,
              then: else_then,
              els: Some(Box::new(Statement::If {
                condition: cond_neither,
                then: else_else,
                els: None,
              }))
            }))
          }))
        }
      },
      Sexp::Atom(Atom::S(s)) if s == "<|>" => {
        let lhs = Box::new(expect_statement(&sexps[1], ctx));
        let rhs = Box::new(expect_statement(&sexps[2], ctx));
        Statement::Relation{lhs, rhs}
      },
      Sexp::Atom(Atom::S(s)) if s == "|>" => {
        let lhs = Box::new(Statement::None);
        let rhs = Box::new(expect_statement(&sexps[1], ctx));
        Statement::Relation{lhs, rhs}
      },
      Sexp::Atom(Atom::S(s)) if s == "<|" => {
        let lhs = Box::new(expect_statement(&sexps[1], ctx));
        let rhs = Box::new(Statement::None);
        Statement::Relation{lhs, rhs}
      },
      Sexp::Atom(Atom::S(s)) if s == "declaration" => {
        Statement::Compound(vec!(BlockItem::Declaration(expect_declaration(sexp, ctx))))
      },
      Sexp::Atom(Atom::S(s)) if s == "guarded-repeat" => {
        expect_guarded_repeat(&sexps, ctx)
      },
      Sexp::Atom(Atom::S(s)) if s == "guarded-repeat-while-rel" => {
        expect_guarded_repeat_while_rel(&sexps, ctx)
      },
      Sexp::Atom(Atom::S(s)) if s == "return" => {
        Statement::Return(Some(Box::new(expect_expression(&sexps[1], ctx))))
      },
      Sexp::Atom(Atom::S(s)) if s == "while-no-body" => {
        let condition = Box::new(expect_expression(&sexps[1], ctx));
        let invariants = expect_invariants(&sexps[2], ctx).values().map(|v| v.clone()).collect();
        Statement::While {
          id: Uuid::new_v4(),
          runoff_link_id: None,
          invariants,
          condition,
          body: None,
          is_runoff: false,
          is_merged: false
        }
      },
      Sexp::Atom(Atom::S(s)) if s == "while" => {
        let condition = Box::new(expect_expression(&sexps[1], ctx));
        let invariants = expect_invariants(&sexps[2], ctx).values().map(|v| v.clone()).collect();
        let body = Some(Box::new(expect_statement(&sexps[3], ctx)));
        Statement::While {
          id: Uuid::new_v4(),
          runoff_link_id: None,
          invariants,
          condition,
          body,
          is_runoff: false,
          is_merged: false
        }
      },
      Sexp::Atom(Atom::S(s)) if s == "while-rel" => {
        expect_while_rel(sexps, ctx)
      },
      _ => Statement::Expression(Box::new(expect_expression(sexp, ctx)))
    },
    _ => Statement::Expression(Box::new(expect_expression(sexp, ctx)))
  }
}

/// Returns a set of invariants indexed by the sexp that encoded each. The HashSet is
/// to aid in de-duping invariants, as Expressions are not hashable. (If they ever
/// become so, the return type of this function can become HashSet<Expression>.)
fn expect_invariants(sexp: &Sexp, ctx: &Context) -> HashMap<String, Expression> {
  match sexp {
    Sexp::List(sexps) => {
      match &sexps[0] {
        Sexp::Atom(Atom::S(s)) if s == "invariants" => {
          let mut invars = HashMap::new();
          for i in 1..sexps.len() {
            invars.insert(sexps[i].to_string(), expect_expression(&sexps[i], ctx));
          }
          invars
        },
        _ => panic!("Expected invariants, got: {}", sexp),
      }
    },
    Sexp::Atom(Atom::S(s)) if s == "invariants" => HashMap::new(),
    _ => panic!("Expected invariants, got: {}", sexp),
  }
}

fn expect_bindings(sexp: &Sexp) -> Vec<(String, Type)> {
  match sexp {
    Sexp::List(sexps) => {
      match &sexps[0] {
        Sexp::Atom(Atom::S(s)) if s == "bindings" => {
          let mut bindings = Vec::new();
          for i in 1..sexps.len() {
            bindings.push(expect_binding(&sexps[i]));
          }
          bindings
        },
        _ => panic!("Expected quantifier bindings, got: {}", sexp),
      }
    },
    Sexp::Atom(Atom::S(s)) if s == "bindings" => Vec::new(),
    _ => panic!("Expected quantifier bindings, got: {}", sexp),
  }
}

fn expect_binding(sexp: &Sexp) -> (String, Type) {
  match sexp {
    Sexp::List(sexps) => {
      match &sexps[0] {
        Sexp::Atom(Atom::S(s)) if s == "binding" => {
          let name = match &sexps[1] {
            Sexp::Atom(Atom::S(s)) => s,
            _ => panic!("Expected quantifier binding, got: {}", sexp),
          };
          let ty = expect_type(&sexps[2]);
          (name.clone(), ty)
        },
        _ => panic!("Expected quantifier binding, got: {}", sexp),
      }
    },
    _ => panic!("Expected quantifier binding, got: {}", sexp),
  }
}

fn expect_while_rel(sexps: &[Sexp], ctx: &Context) -> Statement {
  let cond1 = expect_expression(&sexps[1], ctx);
  let cond2 = expect_expression(&sexps[2], ctx);
  let conj = Expression::Binop {
    lhs: Box::new(cond1.clone()),
    rhs: Box::new(cond2.clone()),
    op: BinaryOp::And,
  };
  let invars1 = expect_invariants(&sexps[3], ctx);
  let invars2 = expect_invariants(&sexps[4], ctx);
  let mut combined_invars: Vec<_> = invars1.values().map(|v| v.clone()).collect();
  for (sexp, expr) in &invars2 {
    if !invars1.contains_key(sexp) {
      combined_invars.push(expr.clone());
    }
  }

  let body1 = expect_statement(&sexps[5], ctx);
  let runoff_body_1 = match ctx.config.assume_name.clone() {
    None => body1.clone(),
    Some(assume_name) => Statement::Compound(vec!(
      BlockItem::Statement(Statement::Expression(Box::new(Expression::Call {
        callee: Box::new(Expression::Identifier{name: assume_name}),
        args: vec!(Expression::Unop{
          expr: Box::new(cond2.clone()),
          op: UnaryOp::Not}),
      }))),
      BlockItem::Statement(body1.clone()),
    )),
  };

  let body2 = expect_statement(&sexps[6], ctx);
  let runoff_body_2 = match ctx.config.assume_name.clone() {
    None => body2.clone(),
    Some(assume_name) => Statement::Compound(vec!(
      BlockItem::Statement(Statement::Expression(Box::new(Expression::Call {
        callee: Box::new(Expression::Identifier{name: assume_name}),
        args: vec!(Expression::Unop{
          expr: Box::new(cond1.clone()),
          op: UnaryOp::Not}),
      }))),
      BlockItem::Statement(body2.clone()),
    )),
  };
  let body = expect_statement(&sexps[7], ctx);

  let runoff_link_id = Some(uuid::Uuid::new_v4());

  let stmts = vec! [
    BlockItem::Statement(Statement::While {
      id: Uuid::new_v4(),
      runoff_link_id: runoff_link_id.clone(),
      is_runoff: false,
      is_merged: true,
      invariants: combined_invars,
      condition: Box::new(conj),
      body: Some(Box::new(body))}),
    BlockItem::Statement(Statement::While {
      id: Uuid::new_v4(),
      runoff_link_id: runoff_link_id.clone(),
      is_runoff: true,
      is_merged: false,
      invariants: invars1.values().map(|v| v.clone()).collect(),
      condition: Box::new(cond1),
      body: Some(Box::new(runoff_body_1))}),
    BlockItem::Statement(Statement::While {
      id: Uuid::new_v4(),
      runoff_link_id: runoff_link_id.clone(),
      is_runoff: true,
      is_merged: false,
      invariants: invars2.values().map(|v| v.clone()).collect(),
      condition: Box::new(cond2),
      body: Some(Box::new(runoff_body_2))}),
  ];
  Statement::Compound(stmts)
}

fn expect_guarded_repeat(sexps: &[Sexp], ctx: &Context) -> Statement {
  let id = expect_string(&sexps[1]);
  let repetitions = *ctx.repetitions.guarded_reps.get(&id).unwrap_or(&1);
  let condition = Box::new(expect_expression(&sexps[2], ctx));
  let body = Box::new(expect_statement(&sexps[3], ctx));
  Statement::GuardedRepeat{id, repetitions, condition, body}
}

fn expect_guarded_repeat_while_rel(sexps: &[Sexp], ctx: &Context) -> Statement {
  let id = expect_string(&sexps[1]);
  let (lhs_reps, rhs_reps) = ctx.repetitions.loop_reps.get(&id).unwrap_or(&(0, 0));

  let cond1 = expect_expression(&sexps[2], ctx);
  let cond2 = expect_expression(&sexps[3], ctx);
  let conj = Expression::Binop {
    lhs: Box::new(cond1.clone()),
    rhs: Box::new(cond2.clone()),
    op: BinaryOp::And,
  };
  let invars1 = expect_invariants(&sexps[4], ctx);
  let invars2 = expect_invariants(&sexps[5], ctx);

  let mut combined_invars: Vec<_> = invars1.values().map(|v| v.clone()).collect();
  for (sexp, expr) in &invars2 {
    if !invars1.contains_key(sexp) {
      combined_invars.push(expr.clone());
    }
  }

  let body1 = expect_statement(&sexps[6], ctx);
  let runoff_body_1 = match ctx.config.assume_name.clone() {
    None => body1.clone(),
    Some(assume_name) => Statement::Compound(vec!(
      BlockItem::Statement(Statement::Expression(Box::new(Expression::Call {
        callee: Box::new(Expression::Identifier{name: assume_name}),
        args: vec!(Expression::Unop{
          expr: Box::new(cond2.clone()),
          op: UnaryOp::Not}),
      }))),
      BlockItem::Statement(body1.clone()),
    )),
  };

  let body2 = expect_statement(&sexps[7], ctx);
  let runoff_body_2 = match ctx.config.assume_name.clone() {
    None => body2.clone(),
    Some(assume_name) => Statement::Compound(vec!(
      BlockItem::Statement(Statement::Expression(Box::new(Expression::Call {
        callee: Box::new(Expression::Identifier{name: assume_name}),
        args: vec!(Expression::Unop{
          expr: Box::new(cond1.clone()),
          op: UnaryOp::Not}),
      }))),
      BlockItem::Statement(body2.clone()),
    )),
  };

  let combined_body = expect_statement(&sexps[7], ctx);

  let repeats = Statement::Relation {
    lhs: Box::new(Statement::GuardedRepeat{
      id: Uuid::new_v4().to_string().replace("-", ""),
      repetitions: *lhs_reps,
      condition: Box::new(cond1.clone()),
      body: Box::new(body1.clone())
    }),
    rhs: Box::new(Statement::GuardedRepeat{
      id: Uuid::new_v4().to_string().replace("-", ""),
      repetitions: *rhs_reps,
      condition: Box::new(cond2.clone()),
      body: Box::new(body2.clone())
    }),
  };

  let body = Statement::Compound(vec!(
    BlockItem::Statement(combined_body),
    BlockItem::Statement(repeats),
  ));

  let runoff_link_id = Some(uuid::Uuid::new_v4());

  let stmts = vec! [
    BlockItem::Statement(Statement::While {
      id: Uuid::new_v4(),
      runoff_link_id: runoff_link_id.clone(),
      is_runoff: false,
      is_merged: true,
      invariants: combined_invars,
      condition: Box::new(conj),
      body: Some(Box::new(body))}),
    BlockItem::Statement(Statement::While {
      id: Uuid::new_v4(),
      runoff_link_id: runoff_link_id.clone(),
      is_runoff: true,
      is_merged: false,
      invariants: invars1.values().map(|v| v.clone()).collect(),
      condition: Box::new(cond1),
      body: Some(Box::new(runoff_body_1))}),
    BlockItem::Statement(Statement::While {
      id: Uuid::new_v4(),
      runoff_link_id: runoff_link_id.clone(),
      is_runoff: true,
      is_merged: false,
      invariants: invars2.values().map(|v| v.clone()).collect(),
      condition: Box::new(cond2),
      body: Some(Box::new(runoff_body_2))}),
  ];
  Statement::Compound(stmts)
}

fn expect_specifiers(sexp: &Sexp) -> Vec<DeclarationSpecifier> {
  match &sexp {
    Sexp::Atom(Atom::S(s)) if s == "specifiers" => Vec::new(),
    Sexp::List(sexps) => match &sexps[0] {
      Sexp::Atom(Atom::S(s)) if s == "specifiers" => {
        sexps[1..].iter()
          .map(expect_declaration_specifier)
          .collect()
      },
      _ => panic!("Expected declaration specifiers, got: {}", sexp),
    }
    _ => panic!("Expected declaration specifiers, got: {}", sexp),
  }
}

fn expect_declaration_specifier(sexp: &Sexp) -> DeclarationSpecifier {
  match &sexp {
    Sexp::List(sexps) => match &sexps[0] {
      Sexp::Atom(Atom::S(s)) if s == "storage-class" => {
        DeclarationSpecifier::StorageClass(expect_storage_class_specifier(&sexps[1]))
      }
      Sexp::Atom(Atom::S(s)) if s == "type" => {
        DeclarationSpecifier::TypeSpecifier(expect_type(&sexps[1]))
      }
      Sexp::Atom(Atom::S(s)) if s == "type-qualifier" => {
        DeclarationSpecifier::TypeQualifier(expect_type_qualifier(&sexps[1]))
      }
      _ => panic!("Expected declaration specifier, got: {}", sexp),
    },
    _ => panic!("Expected declaration specifier, got: {}", sexp),
  }
}

fn expect_type(sexp: &Sexp) -> Type {
  match &sexp {
    Sexp::Atom(Atom::S(ty)) => match ty.as_str() {
      "bool" => Type::Bool,
      "double" => Type::Double,
      "float" => Type::Float,
      "int" => Type::Int,
      "void" => Type::Void,
      _ => panic!("Unknown type: {}", ty),
    },
    _ => panic!("Expected type, got: {}", sexp)
  }
}

fn expect_type_qualifier(sexp: &Sexp) -> TypeQualifier {
  match &sexp {
    Sexp::Atom(Atom::S(ty)) => match ty.as_str() {
      "const" => TypeQualifier::Const,
      _ => panic!("Unknown type qualifier: {}", ty),
    },
    _ => panic!("Expected type qualifier, got: {}", sexp)
  }
}

fn expect_storage_class_specifier(sexp: &Sexp) -> StorageClassSpecifier {
  match &sexp {
    Sexp::Atom(Atom::S(scs)) => match scs.as_str() {
      "extern" => StorageClassSpecifier::Extern,
      _ => panic!("Expected storage class specifier, got: {}", scs),
    },
    _ => panic!("Expected storage class specifier, got: {}", sexp),
  }
}

fn expect_declaration(sexp: &Sexp, ctx: &Context) -> Declaration {
  match &sexp {
    Sexp::List(sexps) => match &sexps[0] {
      Sexp::Atom(Atom::S(s)) if s == "declaration" => {
        let specifiers = expect_specifiers(&sexps[1]);
        let declarator = expect_declarator(&sexps[2], ctx);
        let initializer = if sexps.len() < 4 {
          None
        } else {
          expect_initializer(&sexps[3], ctx)
        };
        Declaration{specifiers, declarator, initializer}
      },
      _ => panic!("Expected declaration, got: {}", sexp),
    },
    _ => panic!("Expected declaration, got: {}", sexp),
  }
}

fn expect_initializer(sexp: &Sexp, ctx: &Context) -> Option<Expression> {
  match &sexp {
    Sexp::Atom(Atom::S(s)) if s == "no-initializer" => None,
    Sexp::List(sexps) => match &sexps[0] {
      Sexp::Atom(Atom::S(s)) if s == "initializer" => {
        let expr = expect_expression(&sexps[1], ctx);
        Some(expr)
      },
      _ => panic!("Expected initializer, got: {}", sexp),
    },
    _ => panic!("Expected initializer, got: {}", sexp),
  }
}

fn expect_declarator(sexp: &Sexp, ctx: &Context) -> Declarator {
  match &sexp {
    Sexp::Atom(Atom::S(name)) => Declarator::Identifier{name: name.clone()},
    Sexp::List(sexps) => match &sexps[0] {
      Sexp::Atom(Atom::S(s)) if s == "unsized-array" => {
        Declarator::Array{name: expect_string(&sexps[1]), sizes: Vec::new()}
      },
      Sexp::Atom(Atom::S(s)) if s == "sized-array" => {
        let sizes = expect_array_sizes(&sexps[2], ctx);
        Declarator::Array{name: expect_string(&sexps[1]), sizes}
      },
      Sexp::Atom(Atom::S(s)) if s == "fun-declarator" => {
        let params = expect_param_decls(&sexps[2], ctx);
        Declarator::Function{name: expect_string(&sexps[1]), params}
      },
      Sexp::Atom(Atom::S(s)) if s == "pointer" => {
        let decl = expect_declarator(&sexps[1], ctx);
        Declarator::Pointer(Box::new(decl))
      },
      _ => panic!("Expected declarator, got: {}", sexp),
    }
    _ => panic!("Expected declarator, got: {}", sexp),
  }
}

fn expect_array_sizes(sexp: &Sexp, ctx: &Context) -> Vec<Expression> {
 match &sexp {
    Sexp::Atom(Atom::S(s)) if s == "array-sizes" => Vec::new(),
    Sexp::List(sexps) => match &sexps[0] {
      Sexp::Atom(Atom::S(s)) if s == "array-sizes" => {
        sexps[1..].iter()
          .map(|x| expect_expression(x, ctx))
          .collect()
      },
      _ => panic!("Expected array sizes, got: {}", sexp),
    },
    _ => panic!("Expected array sizes, got: {}", sexp),
  }
}

fn expect_param_decls(sexp: &Sexp, ctx: &Context) -> Vec<ParameterDeclaration> {
  match &sexp {
    Sexp::Atom(Atom::S(s)) if s == "params" => Vec::new(),
    Sexp::List(sexps) => match &sexps[0] {
      Sexp::Atom(Atom::S(s)) if s == "params" => {
        sexps[1..].iter()
          .map(|x| expect_param_declaration(x, ctx))
          .collect()
      },
      _ => panic!("Expected params, got: {}", sexp),
    },
    _ => panic!("Expected params, got: {}", sexp),
  }
}

fn expect_param_declaration(sexp: &Sexp, ctx: &Context) -> ParameterDeclaration {
  match &sexp {
    Sexp::List(sexps) => match &sexps[0] {
      Sexp::Atom(Atom::S(s)) if s == "param-declaration" => {
        let specifiers = expect_specifiers(&sexps[1]);
        let declarator = if sexps.len() > 2 {
          Some(expect_declarator(&sexps[2], ctx))
        } else { None };
        ParameterDeclaration{specifiers, declarator}
      },
      _ => panic!("Expected declaration, got: {}", sexp),
    },
    _ => panic!("Expected params, got: {}", sexp),
  }
}

fn expect_args(sexp: &Sexp, ctx: &Context) -> Vec<Expression> {
  match &sexp {
    Sexp::Atom(Atom::S(s)) if s == "args" => Vec::new(),
    Sexp::List(sexps) => match &sexps[0] {
      Sexp::Atom(Atom::S(s)) if s == "args" => {
        sexps[1..].iter()
          .map(|x| expect_expression(x, ctx))
          .collect()
      },
      _ => panic!("Expected args, got: {}", sexp),
    },
    _ => panic!("Expected args, got: {}", sexp),
  }
}

fn expect_block_item(sexp: &Sexp, ctx: &Context) -> BlockItem {
  match &sexp {
    Sexp::List(sexps) => match &sexps[0] {
      Sexp::Atom(Atom::S(s)) if s == "declaration" => {
        let declaration = expect_declaration(sexp, ctx);
        BlockItem::Declaration(declaration)
      },
      _ => BlockItem::Statement(expect_statement(sexp, ctx)),
    },
    _ => BlockItem::Statement(expect_statement(sexp, ctx)),
  }
}

fn expect_string(sexp: &Sexp) -> String {
  match &sexp {
    Sexp::Atom(Atom::S(s)) => s.clone(),
    _ => panic!("Expected string literal, got: {}", sexp)
  }
}
