use crate::crel::ast::*;
use crate::crel::fundef::*;
use crate::spec::condition::*;
use crate::spec::to_crel::*;
use crate::elaenia::elaenia_spec::*;
use crate::elaenia::tasks::elaenia_context::*;
use crate::workflow::context::*;
use crate::workflow::task::*;
use std::collections::HashMap;

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
    let mut spec_inserter = SpecInserter2::new(&spec);
    let mapped_crel = spec_inserter.insert_specs_crel(&crel);
    context.accept_aligned_crel(mapped_crel);
    for gen in spec_inserter.added_choice_gens {
      context.accept_choice_gen(gen);
    }
    for fun in spec_inserter.added_choice_funs {
      context.accept_choice_fun(fun);
    }
  }
}

struct SpecInserter2<'a> {
  spec: &'a ElaeniaSpec,
  added_choice_funs: Vec<FunDef>,
  added_choice_gens: Vec<FunDef>,
  current_choice_id: u32,
  current_scope: HashMap<String, (Type, bool)>,
}

impl <'a> SpecInserter2<'a> {
  fn new(spec: &'a ElaeniaSpec) -> SpecInserter2<'a> {
    SpecInserter2 {
      spec,
      added_choice_funs: Vec::new(),
      added_choice_gens: Vec::new(),
      current_choice_id: 0,
      current_scope: HashMap::new(),
    }
  }

  fn add_to_scope(&mut self,
                  specifiers: &Vec<DeclarationSpecifier>,
                  declarator: &Declarator,
                  initialized: bool) {
    for specifier in specifiers {
      match &specifier {
        DeclarationSpecifier::TypeSpecifier(ty) => {
          match declarator {
            Declarator::Identifier{name} => {
              self.current_scope.insert(name.clone(), (ty.clone(), initialized));
            },
            Declarator::Array{name, ..} => {
              self.current_scope.insert(name.clone(), (ty.clone(), initialized));
            },
            _ => (),
          }
        },
        _ => (),
      }
    }
  }

  fn mark_initialized(&mut self, name: &String) {
    match self.current_scope.get(name) {
      Some((ty, false)) => {
        self.current_scope.insert(name.clone(), (ty.clone(), true));
      },
      _ => (),
    }
  }

  pub fn insert_specs_crel(&mut self, crel: &CRel) -> CRel {
    match crel {
      CRel::Declaration(decl) => {
        self.add_to_scope(&decl.specifiers, &decl.declarator, decl.initializer.is_some());
        CRel::Declaration(decl.clone())
      },
      CRel::FunctionDefinition{ specifiers, name, params, body } => {
        let outer_scope = self.current_scope.clone();
        for ParameterDeclaration{specifiers, declarator} in params {
          declarator.as_ref().map(|decl| self.add_to_scope(specifiers, decl, true));
        }
        let new_body = self.insert_specs_statement(body);
        self.current_scope = outer_scope;
        CRel::FunctionDefinition {
          specifiers: specifiers.clone(),
          name: name.clone(),
          params: params.clone(),
          body: Box::new(new_body),
        }
      },
      CRel::Seq(crels) => {
        CRel::Seq(crels.into_iter()
                  .map(|crel| self.insert_specs_crel(crel))
                  .collect())
      },
    }
  }

  pub fn insert_specs_statement(&mut self, stmt: &Statement) -> Statement {
    match stmt {
      Statement::Assert(expr) => {
        Statement::Assert(Box::new(self.insert_specs_expression(expr)))
      },
      Statement::Assume(expr) => {
        Statement::Assert(Box::new(self.insert_specs_expression(expr)))
      },
      Statement::BasicBlock(items) => {
        Statement::BasicBlock(items.into_iter()
                              .map(|item| self.insert_specs_block_item(item))
                              .collect())
      },
      Statement::Break => {
        Statement::Break
      },
      Statement::Compound(items) => {
        Statement::Compound(items.into_iter()
                            .map(|item| self.insert_specs_block_item(item))
                            .collect())
      },
      Statement::Expression(expr) => {
        Statement::Expression(Box::new(self.insert_specs_expression(expr)))
      },
      Statement::GuardedRepeat{ id, repetitions, condition, body } => {
        let outer_scope = self.current_scope.clone();
        let new_body = self.insert_specs_statement(body);
        self.current_scope = outer_scope;
        Statement::GuardedRepeat {
          id: id.clone(),
          repetitions: repetitions.clone(),
          condition: condition.clone(),
          body: Box::new(new_body),
        }
      },
      Statement::If{ condition, then, els } => {
        let outer_scope = self.current_scope.clone();
        let new_then = self.insert_specs_statement(then);
        self.current_scope = outer_scope.clone();
        let new_els = els.as_ref().map(|els| {
          Box::new(self.insert_specs_statement(els))
        });
        self.current_scope = outer_scope;
        Statement::If {
          condition: condition.clone(),
          then: Box::new(new_then),
          els: new_els,
        }
      },
      Statement::None => {
        Statement::None
      },
      Statement::Relation{ lhs, rhs } => {
        let outer_scope = self.current_scope.clone();
        let new_lhs = self.insert_specs_statement(lhs);
        // Keep LHS scope in RHS.
        let new_rhs = self.insert_specs_statement(rhs);
        self.current_scope = outer_scope;
        Statement::Relation {
          lhs: Box::new(new_lhs),
          rhs: Box::new(new_rhs),
        }
      },
      Statement::Return(val) => {
        Statement::Return(val.as_ref().map(|v| {
          Box::new(self.insert_specs_expression(v))
        }))
      },
      Statement::While{ id, runoff_link_id, invariants,
                        condition, body, is_runoff, is_merged } => {
        let outer_scope = self.current_scope.clone();
        let new_body = body.as_ref().map(|body| {
          Box::new(self.insert_specs_statement(body))
        });
        self.current_scope = outer_scope;
        Statement::While {
          id: id.clone(),
          runoff_link_id: runoff_link_id.clone(),
          invariants: invariants.clone(),
          condition: condition.clone(),
          body: new_body,
          is_runoff: is_runoff.clone(),
          is_merged: is_merged.clone(),
        }
      }
    }
  }

  pub fn insert_specs_expression(&mut self, expr: &Expression) -> Expression {
    match expr {
      Expression::Statement(stmt) => {
        Expression::Statement(Box::new(self.insert_specs_statement(stmt)))
      },
      Expression::Binop{lhs, rhs, op} if *op == BinaryOp::Assign => {
        match *lhs.clone() {
          Expression::Identifier{ name } => {
            let new_expr = match *rhs.clone() {
              Expression::Call{callee, ..} => {
                self.handle_fun_call(expr, &name, &*callee)
              },
              _ => expr.clone(),
            };
            self.mark_initialized(&name);
            new_expr
          },
          _ => expr.clone(),
        }
      },
      _ => expr.clone(),
    }
  }

  pub fn insert_specs_block_item(&mut self, item: &BlockItem) -> BlockItem {
    match item {
      BlockItem::Declaration(decl) => {
        self.add_to_scope(&decl.specifiers, &decl.declarator, decl.initializer.is_some());
        BlockItem::Declaration(decl.clone())
      },
      BlockItem::Statement(stmt) => {
        BlockItem::Statement(self.insert_specs_statement(stmt))
      },
    }
  }

  fn handle_fun_call(&mut self,
                     call_expr: &Expression,
                     assignee_name: &String,
                     callee: &Expression) -> Expression {
    match callee {
      Expression::Identifier{name} => {
        if assignee_name.starts_with("l_") {
          self.surround_aspec(assignee_name, &name, call_expr)
        } else if assignee_name.starts_with("r_") {
          self.surround_espec(assignee_name, &name, call_expr, 3)
        } else {
          call_expr.clone()
        }
      },
      _ => call_expr.clone(),
    }
  }

  fn surround_aspec(&mut self,
                    assignee_name: &String,
                    fun_name: &String,
                    expr: &Expression)
                    -> Expression {
    let aspec = self.spec.lookup_aspec(&fun_name);
    match aspec {
      Some(aspec) => {
        let assert_pre = spec_cond_to_expression(&aspec.pre, &assignee_name, StatementKind::Assert);
        let assume_post = spec_cond_to_expression(&aspec.post, &assignee_name, StatementKind::Assume);
        Expression::Statement(Box::new(Statement::Compound(vec!(
          BlockItem::Statement(assert_pre),
          BlockItem::Statement(Statement::Expression(Box::new(expr.clone()))),
          BlockItem::Statement(assume_post),
        ))))
      },
      None => expr.clone(),
    }
  }

  fn surround_espec(&mut self,
                    assignee_name: &String,
                    fun_name: &String,
                    expr: &Expression,
                    depth: i32)
                    -> Expression {
    let espec = self.spec.lookup_espec(&fun_name);
    match espec {
      Some(espec) => {
        let mut choice_decls = espec.choice_vars.iter()
          .map(|chvar| {
            self.current_choice_id += 1;
            let choice_fun_name = format!("_choice_{}_{}", chvar, self.current_choice_id);
            let choice_gen_name = format!("_gen_choice_{}_{}", chvar, self.current_choice_id);

            let choice_fun_params = self.current_scope.clone().into_iter()
              .filter(|(_,(_, initialized))| *initialized)
              .map(|(name, (ty, _))| {
                ParameterDeclaration {
                  specifiers: vec!(DeclarationSpecifier::TypeSpecifier(ty)),
                  declarator: Some(Declarator::Identifier{ name }),
                }
              }).collect::<Vec<_>>();

            let choice_fun_args = self.current_scope.clone().into_iter()
              .filter(|(_,(_, initialized))| *initialized)
              .map(|(name, _)| Expression::Identifier{name})
              .collect::<Vec<_>>();

            let mut choice_gen_params = vec!(ParameterDeclaration {
              specifiers: vec!(DeclarationSpecifier::TypeSpecifier(Type::Int)),
              declarator: Some(Declarator::Identifier{ name: "depth".to_string() }),
            });
            choice_gen_params.append(&mut choice_fun_params.clone());

            let mut choice_gen_args = vec!(Expression::ConstInt(depth));
            choice_gen_args.append(&mut choice_fun_args.clone());

            let decl = Declaration {
              specifiers: vec!(DeclarationSpecifier::TypeSpecifier(Type::Int)),
              declarator: Declarator::Identifier{name: chvar.clone()},
              initializer: Some(Expression::Call {
                callee: Box::new(Expression::Identifier{ name: choice_fun_name.clone() }),
                args: choice_fun_args.clone(),
              })
            };
            self.added_choice_funs.push(FunDef {
              specifiers: vec!(DeclarationSpecifier::TypeSpecifier(Type::Int)),
              name: choice_fun_name.clone(),
              params: choice_fun_params.clone(),
              body: Statement::Return(Some(Box::new(Expression::Call {
                callee: Box::new(Expression::Identifier{ name: choice_gen_name.clone() }),
                args: choice_gen_args.clone(),
              }))),
            });
            self.added_choice_gens.push(FunDef {
              specifiers: vec!(DeclarationSpecifier::TypeSpecifier(Type::Int)),
              name: choice_gen_name.clone(),
              params: choice_gen_params.clone(),
              body: Statement::Return(Some(Box::new(Expression::SketchHole))),
            });
            BlockItem::Declaration(decl)
          })
          .collect::<Vec<_>>();
        let assert_pre = spec_cond_to_expression(&espec.pre, &assignee_name, StatementKind::Assert);
        let assume_post = spec_cond_to_expression(&espec.post, &assignee_name, StatementKind::Assume);

        let mut statements = Vec::new();
        statements.append(&mut choice_decls);
        statements.push(BlockItem::Statement(assert_pre));
        statements.push(BlockItem::Statement(Statement::Expression(Box::new(expr.clone()))));
        statements.push(BlockItem::Statement(assume_post));
        Expression::Statement(Box::new(Statement::Compound(statements)))
      },
      None => expr.clone(),
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
