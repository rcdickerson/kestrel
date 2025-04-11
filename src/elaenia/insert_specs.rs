use crate::crel::ast::*;
use crate::crel::fundef::*;
use crate::crel::mapper::*;
use crate::spec::condition::*;
use crate::spec::to_crel::*;
use crate::elaenia::elaenia_context::*;
use crate::elaenia::elaenia_spec::*;
use crate::workflow::context::*;
use crate::workflow::task::*;

pub struct InsertSpecs { }

impl InsertSpecs {
  pub fn new() -> Self {
    InsertSpecs {}
  }
}

impl Task<ElaeniaContext> for InsertSpecs {
  fn name(&self) -> String { "insert-elaenia-specs".to_string() }
  fn run(&self, context: &mut ElaeniaContext) {
    let crel = context.aligned_crel().clone().expect("Missing aligned CRel");
    let spec = context.spec().clone();
    let mut spec_inserter = SpecInserter::new(&spec);
    let mapped_crel = crel.map(&mut spec_inserter);
    context.accept_aligned_crel(mapped_crel);
    for gen in spec_inserter.added_choice_gens {
      context.accept_choice_gen(gen);
    }
    for fun in spec_inserter.added_choice_funs {
      context.accept_choice_fun(fun);
    }
  }
}

struct SpecInserter<'a> {
  spec: &'a ElaeniaSpec,
  added_choice_funs: Vec<FunDef>,
  added_choice_gens: Vec<FunDef>,
  choice_id: u32,
}

impl <'a> SpecInserter<'a> {
  fn new(spec: &'a ElaeniaSpec) -> SpecInserter<'a> {
    SpecInserter {
      spec,
      added_choice_funs: Vec::new(),
      added_choice_gens: Vec::new(),
      choice_id: 0
    }
  }
}

impl <'a> CRelMapper for SpecInserter<'a> {
  fn map_expression(&mut self, expr: &Expression) -> Expression {
    match expr {
      Expression::Binop{lhs, rhs, op} => match (*lhs.clone(), *rhs.clone(), op) {
        (Expression::Identifier{name},
         Expression::Call{callee, args},
         BinaryOp::Assign) => {
          let lhs_name = name;
          match *callee {
            Expression::Identifier{name} => {
              if lhs_name.starts_with("l_") {
                let aspec = self.spec.lookup_aspec(&name);
                match aspec {
                  Some(aspec) => {
                    let assert_pre = spec_cond_to_expression(&aspec.pre, &lhs_name, StatementKind::Assert);
                    let assume_post = spec_cond_to_expression(&aspec.post, &lhs_name, StatementKind::Assume);
                    Expression::Statement(Box::new(Statement::Compound(vec!(
                      BlockItem::Statement(assert_pre),
                      BlockItem::Statement(Statement::Expression(Box::new(expr.clone()))),
                      BlockItem::Statement(assume_post),
                    ))))
                  },
                  None => expr.clone(),
                }
              } else if lhs_name.starts_with("r_") {
                let espec = self.spec.lookup_espec(&name);
                match espec {
                  Some(espec) => {
                    let mut choice_decls = espec.choice_vars.iter()
                      .map(|chvar| {
                        self.choice_id += 1;
                        let choice_fun_name = format!("_choice_{}_{}", chvar, self.choice_id);
                        let choice_gen_name = format!("_gen_choice_{}_{}", chvar, self.choice_id);
                        let decl = Declaration {
                          specifiers: vec!(DeclarationSpecifier::TypeSpecifier(Type::Int)),
                          //declarator: Declarator::Identifier{name: format!("_choice_var_{}", chvar)},
                          declarator: Declarator::Identifier{name: chvar.clone()},
                          initializer: Some(Expression::Call {
                            callee: Box::new(Expression::Identifier{ name: choice_fun_name.clone() }),
                            args: vec!(),
                          })
                        };
                        self.added_choice_funs.push(FunDef {
                          specifiers: vec!(DeclarationSpecifier::TypeSpecifier(Type::Int)),
                          name: choice_fun_name.clone(),
                          params: Vec::new(),
                          body: Statement::Return(Some(Box::new(Expression::Call {
                            callee: Box::new(Expression::Identifier{ name: choice_gen_name.clone() }),
                            args: Vec::new(),
                          }))),
                        });
                        self.added_choice_gens.push(FunDef {
                          specifiers: vec!(DeclarationSpecifier::TypeSpecifier(Type::Int)),
                          name: choice_gen_name.clone(),
                          params: Vec::new(),
                          body: Statement::Return(Some(Box::new(Expression::SketchHole))),
                        });
                        BlockItem::Declaration(decl)
                      })
                      .collect::<Vec<_>>();
                    let assert_pre = spec_cond_to_expression(&espec.pre, &lhs_name, StatementKind::Assert);
                    let assume_post = spec_cond_to_expression(&espec.post, &lhs_name, StatementKind::Assume);

                    let mut statements = Vec::new();
                    statements.append(&mut choice_decls);
                    statements.push(BlockItem::Statement(assert_pre));
                    statements.push(BlockItem::Statement(Statement::Expression(Box::new(expr.clone()))));
                    statements.push(BlockItem::Statement(assume_post));
                    Expression::Statement(Box::new(Statement::Compound(statements)))
                  },
                  None => expr.clone(),
                }
              } else {
                expr.clone()
              }
            },
            _ => expr.clone(),
          }
        },
        _ => expr.clone(),
      },
      _ => expr.clone(),
    }
  }
}

fn spec_cond_to_expression(cond: &KestrelCond, assignee_name: &String, kind: StatementKind) -> Statement {
  let with_assignee = replace_ret_val_kcond(cond.clone(),
                                            &CondAExpr::Var(assignee_name.clone()));
  with_assignee.to_crel(kind)
}

fn replace_ret_val_kcond(cond: KestrelCond, replacement: &CondAExpr) -> KestrelCond {
  match cond {
    KestrelCond::ForLoop { index_var, start, end, body } => KestrelCond::ForLoop {
      index_var: index_var.clone(),
      start: replace_ret_val_aexpr(start, replacement),
      end: replace_ret_val_aexpr(end, replacement),
      body: Box::new(replace_ret_val_kcond(*body, replacement))
    },
    KestrelCond::BExpr(bexpr) => KestrelCond::BExpr(replace_ret_val_bexpr(bexpr, replacement)),
    KestrelCond::And{lhs, rhs} => KestrelCond::And {
      lhs: Box::new(replace_ret_val_kcond(*lhs, replacement)),
      rhs: Box::new(replace_ret_val_kcond(*rhs, replacement)),
    }
  }
}

fn replace_ret_val_bexpr(bexpr: CondBExpr, replacement: &CondAExpr) -> CondBExpr {
  match bexpr {
    CondBExpr::True => bexpr,
    CondBExpr::False => bexpr,
    CondBExpr::Unop{bexp, op} => CondBExpr::Unop {
      bexp: Box::new(replace_ret_val_bexpr(*bexp, replacement)),
      op
    },
    CondBExpr::BinopA{lhs, rhs, op} => CondBExpr::BinopA {
      lhs: replace_ret_val_aexpr(lhs, replacement),
      rhs: replace_ret_val_aexpr(rhs, replacement),
      op,
    },
    CondBExpr::BinopB{lhs, rhs, op} => CondBExpr::BinopB {
      lhs: Box::new(replace_ret_val_bexpr(*lhs, replacement)),
      rhs: Box::new(replace_ret_val_bexpr(*rhs, replacement)),
      op,
    },
    CondBExpr::Forall{bindings, condition} => CondBExpr::Forall {
      bindings: bindings.clone(),
      condition: Box::new(replace_ret_val_bexpr(*condition, replacement)),
    },
    CondBExpr::Predicate{name, args} => CondBExpr::Predicate {
      name: name.clone(),
      args: args.iter()
        .map(|arg| replace_ret_val_aexpr(arg.clone(), replacement))
        .collect(),
    },
  }
}

fn replace_ret_val_aexpr(aexpr: CondAExpr, replacement: &CondAExpr) -> CondAExpr {
  match aexpr {
    CondAExpr::Var(_) => aexpr,
    CondAExpr::ReturnValue => replacement.clone(),
    CondAExpr::QualifiedVar{..} => aexpr,
    CondAExpr::Int(_) => aexpr,
    CondAExpr::Float(_) => aexpr,
    CondAExpr::Unop{aexp, op} => CondAExpr::Unop{
      aexp: Box::new(replace_ret_val_aexpr(*aexp, replacement)),
      op
    },
    CondAExpr::Binop{lhs, rhs, op} => CondAExpr::Binop {
      lhs: Box::new(replace_ret_val_aexpr(*lhs, replacement)),
      rhs: Box::new(replace_ret_val_aexpr(*rhs, replacement)),
      op,
    },
    CondAExpr::FunCall{name, args} => CondAExpr::FunCall {
      name,
      args: args.iter()
        .map(|arg| replace_ret_val_aexpr(arg.clone(), replacement))
        .collect(),
    }
  }
}
