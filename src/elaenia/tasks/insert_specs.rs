use crate::crel::ast::*;
use crate::crel::fundef::*;
use crate::crel::mapper::*;
use crate::names::MapVars;
use crate::spec::condition::*;
use crate::spec::to_crel::*;
use crate::elaenia::elaenia_spec::*;
use crate::elaenia::tasks::elaenia_context::*;
use crate::workflow::context::*;
use crate::workflow::task::*;
use std::collections::HashMap;

pub struct InsertSpecs {
  grammar_depth: u32,
}

impl InsertSpecs {
  pub fn new(grammar_depth: u32) -> Self {
    InsertSpecs {
      grammar_depth,
    }
  }

  pub fn set_grammar_depth(&mut self, depth: u32) {
    self.grammar_depth = depth;
  }
}

impl Task<ElaeniaContext> for InsertSpecs {
  fn name(&self) -> String { "insert-elaenia-specs".to_string() }
  fn run(&self, context: &mut ElaeniaContext) {
    let crel = context.aligned_crel().clone().expect("Missing aligned CRel");
    context.accept_aligned_crel_no_spec(crel.clone());
    let spec = context.spec().clone();
    let mut spec_inserter = SpecInserter::new(&spec, self.grammar_depth);
    let mapped_crel = spec_inserter.insert_specs_crel(&crel);
    context.accept_aligned_crel(mapped_crel);
    for gen in spec_inserter.added_choice_gens {
      context.accept_choice_gen(gen);
    }
    for fun in spec_inserter.added_choice_funs {
      context.accept_choice_fun(fun);
    }
    for havoc in spec_inserter.added_havoc_funs {
      context.accept_havoc_fun(havoc);
    }
  }
}

struct SpecInserter<'a> {
  spec: &'a ElaeniaSpec,
  added_choice_funs: Vec<FunDef>,
  added_choice_gens: Vec<FunDef>,
  added_havoc_funs: Vec<FunDef>,
  current_id: u32,
  scope_identifiers: HashMap<String, (Type, bool)>,
  scope_arrays: HashMap<String, (Type, Vec<Expression>, bool)>,
  grammar_depth: u32,
}

impl <'a> SpecInserter<'a> {
  fn new(spec: &'a ElaeniaSpec, grammar_depth: u32) -> SpecInserter<'a> {
    SpecInserter {
      spec,
      added_choice_funs: Vec::new(),
      added_choice_gens: Vec::new(),
      added_havoc_funs: Vec::new(),
      current_id: 0,
      scope_identifiers: HashMap::new(),
      scope_arrays: HashMap::new(),
      grammar_depth,
    }
  }

  fn next_id(&mut self) -> u32 {
    self.current_id += 1;
    self.current_id
  }

  fn make_havoc(&mut self) -> &FunDef {
    let id = self.next_id();
    let def = FunDef {
      specifiers: vec!(DeclarationSpecifier::TypeSpecifier(Type::Int)),
      name: format!("havoc_{}", id),
      params: self.in_scope_params(),
      body: Statement::None,
    };
    self.added_havoc_funs.push(def);
    self.added_havoc_funs.last().unwrap()
  }

  fn in_scope_params(&self) -> Vec<ParameterDeclaration> {
    let mut params = self.scope_identifiers.clone().into_iter()
      .filter(|(name,(_, initialized))| !name.ends_with("_in") && *initialized)
      .map(|(name, (ty, _))| {
        ParameterDeclaration {
          specifiers: vec!(DeclarationSpecifier::TypeSpecifier(ty)),
          declarator: Some(Declarator::Identifier{ name }),
        }
      }).collect::<Vec<_>>();
    let mut array_params = self.scope_arrays.clone().into_iter()
      .filter(|(name,(_, _, initialized))| !name.ends_with("_in") && *initialized)
      .map(|(name, (ty, sizes, _))| {
        ParameterDeclaration {
          specifiers: vec!(DeclarationSpecifier::TypeSpecifier(ty)),
          declarator: Some(Declarator::Array{ name, sizes }),
        }
      }).collect();
    params.append(&mut array_params);
    params
  }

  fn in_scope_args(&self) -> Vec<Expression> {
    let mut args = self.scope_identifiers.clone().into_iter()
      .filter(|(name,(_, initialized))| !name.ends_with("_in") && *initialized)
      .map(|(name, _)| Expression::Identifier{name})
      .collect::<Vec<_>>();
    let mut array_args = self.scope_arrays.clone().into_iter()
      .filter(|(name,(_, _, initialized))| !name.ends_with("_in") && *initialized)
      .map(|(name, _)| Expression::Identifier{name})
      .collect();
    args.append(&mut array_args);
    args
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
              self.scope_identifiers.insert(name.clone(), (ty.clone(), initialized));
            },
            Declarator::Array{name, sizes} => {
              self.scope_arrays.insert(name.clone(), (ty.clone(), sizes.clone(), initialized));
            },
            _ => (),
          }
        },
        _ => (),
      }
    }
  }

  fn mark_initialized(&mut self, name: &String) {
    match self.scope_identifiers.get(name) {
      Some((ty, false)) => {
        self.scope_identifiers.insert(name.clone(), (ty.clone(), true));
      },
      _ => match self.scope_arrays.get(name) {
        Some((ty, sizes, false)) => {
          self.scope_arrays.insert(name.clone(), (ty.clone(), sizes.clone(), true));
        },
        _ => (),
      }
    }
  }

  pub fn insert_specs_crel(&mut self, crel: &CRel) -> CRel {
    match crel {
      CRel::Declaration(decl) => {
        self.add_to_scope(&decl.specifiers, &decl.declarator, decl.initializer.is_some());
        CRel::Declaration(decl.clone())
      },
      CRel::FunctionDefinition{ specifiers, name, params, body } => {
        let outer_scope_identifiers = self.scope_identifiers.clone();
        let outer_scope_arrays = self.scope_arrays.clone();
        for ParameterDeclaration{specifiers, declarator} in params {
          declarator.as_ref().map(|decl| self.add_to_scope(specifiers, decl, true));
        }
        let new_body = self.insert_specs_statement(body);
        self.scope_identifiers = outer_scope_identifiers;
        self.scope_arrays = outer_scope_arrays;
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
        Statement::Assume(Box::new(self.insert_specs_expression(expr)))
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
        let outer_scope = self.scope_identifiers.clone();
        let new_body = self.insert_specs_statement(body);
        self.scope_identifiers = outer_scope;
        Statement::GuardedRepeat {
          id: id.clone(),
          repetitions: repetitions.clone(),
          condition: condition.clone(),
          body: Box::new(new_body),
        }
      },
      Statement::If{ condition, then, els } => {
        let outer_scope = self.scope_identifiers.clone();
        let new_then = self.insert_specs_statement(then);
        self.scope_identifiers = outer_scope.clone();
        let new_els = els.as_ref().map(|els| {
          Box::new(self.insert_specs_statement(els))
        });
        self.scope_identifiers = outer_scope;
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
        let new_lhs = self.insert_specs_statement(lhs);
        let new_rhs = self.insert_specs_statement(rhs);
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
        let outer_scope = self.scope_identifiers.clone();
        let new_body = body.as_ref().map(|body| {
          Box::new(self.insert_specs_statement(body))
        });
        self.scope_identifiers = outer_scope;
        Statement::While {
          id: id.clone(),
          runoff_link_id: runoff_link_id.clone(),
          invariants: invariants.clone(),
          condition: condition.clone(),
          body: new_body,
          is_runoff: is_runoff.clone(),
          is_merged: is_merged.clone(),
        }
      },
      Statement::WhileRel {
        id,
        unroll_left,
        unroll_right,
        stutter_left,
        stutter_right,
        invariants_left,
        invariants_right,
        condition_left,
        condition_right,
        body_left,
        body_right,
        body_merged,
      } => {
        let outer_scope = self.scope_identifiers.clone();
        let new_body_left = body_left.as_ref().map(|body| {
          Box::new(self.insert_specs_statement(body))
        });
        self.scope_identifiers = outer_scope.clone();
        let new_body_right = body_right.as_ref().map(|body| {
          Box::new(self.insert_specs_statement(body))
        });
        self.scope_identifiers = outer_scope.clone();
        let new_body_merged = body_merged.as_ref().map(|body| {
          Box::new(self.insert_specs_statement(body))
        });
        self.scope_identifiers = outer_scope;

        Statement::WhileRel {
          id: id.clone(),
          unroll_left: *unroll_left,
          unroll_right: *unroll_right,
          stutter_left: *stutter_left,
          stutter_right: *stutter_right,
          invariants_left: invariants_left.clone(),
          invariants_right: invariants_right.clone(),
          condition_left: condition_left.clone(),
          condition_right: condition_right.clone(),
          body_left: new_body_left,
          body_right: new_body_right,
          body_merged: new_body_merged,
        }
      },
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
              Expression::Call{callee, args} => {
                self.handle_fun_call(expr, &name, &args, &*callee)
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
      BlockItem::Declaration(decl) => match &decl.initializer {
        Some(Initializer::Expression(init_expr)) => {
          self.add_to_scope(&decl.specifiers, &decl.declarator, true);
          let initialize_expr = Expression::Binop {
            lhs: Box::new(Expression::Identifier{name: decl.declarator.name()}),
            rhs: Box::new(init_expr.clone()),
            op: BinaryOp::Assign,
          };
          BlockItem::Statement(Statement::Compound(vec!(
            BlockItem::Declaration(Declaration {
              specifiers: decl.specifiers.clone(),
              declarator: decl.declarator.clone(),
              initializer: None,
            }),
            BlockItem::Statement(Statement::Expression(
              Box::new(self.insert_specs_expression(&initialize_expr)))),
          )))
        },
        _ => {
          self.add_to_scope(&decl.specifiers, &decl.declarator, decl.initializer.is_some());
          BlockItem::Declaration(decl.clone())
        },
      },
      BlockItem::Statement(stmt) => {
        BlockItem::Statement(self.insert_specs_statement(stmt))
      },
    }
  }

  fn handle_fun_call(&mut self,
                     call_expr: &Expression,
                     assignee_name: &String,
                     args: &Vec<Expression>,
                     callee: &Expression)
                     -> Expression {
    match callee {
      Expression::Identifier{name} => {
        if assignee_name.starts_with("l_") {
          self.surround_aspec(assignee_name, &name, args, call_expr)
        } else if assignee_name.starts_with("r_") {
          self.surround_espec(assignee_name, &name, args, call_expr)
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
                    args: &Vec<Expression>,
                    expr: &Expression)
                    -> Expression {
    let aspec = self.spec.lookup_aspec(&fun_name);
    match aspec {
      Some(aspec) => {
        let mut param_replacements = HashMap::new();
        for (param, arg) in aspec.params.iter().zip(args) {
          param_replacements.insert(param.name().clone(), arg.clone());
        }
        let assert_pre = spec_cond_to_expression(
          &aspec.pre, &assignee_name, StatementKind::Assert)
          .map(&mut ReplaceIdentifiers::new(param_replacements.clone()));
        let assume_post = spec_cond_to_expression(
          &aspec.post, &assignee_name, StatementKind::Assume)
          .map(&mut ReplaceIdentifiers::new(param_replacements));
        let havoc = self.make_havoc();
        let call_havoc = Expression::Binop {
          lhs: Box::new(Expression::Identifier{name: assignee_name.clone()}),
          rhs: Box::new(Expression::Call {
            callee: Box::new(Expression::Identifier{name: havoc.name.clone()}),
            args: self.in_scope_args(),
          }),
          op: BinaryOp::Assign,
        };
        Expression::Statement(Box::new(Statement::Compound(vec!(
          BlockItem::Statement(assert_pre),
          BlockItem::Statement(Statement::Expression(Box::new(call_havoc))),
          BlockItem::Statement(assume_post),
        ))))
      },
      None => expr.clone(),
    }
  }

  fn surround_espec(&mut self,
                    assignee_name: &String,
                    fun_name: &String,
                    args: &Vec<Expression>,
                    expr: &Expression)
                    -> Expression {
    // Only conintue if there is an existential spec for this function.
    let espec_lookup = self.spec.lookup_espec(&fun_name);
    if espec_lookup.is_none() { return expr.clone(); }
    let espec = espec_lookup.unwrap();

    // Generators will take in a parameter for maximum AST depth.
    let prepend_depth_param = |params: &Vec<ParameterDeclaration>| {
      let mut with_depth = vec!(ParameterDeclaration {
        specifiers: vec!(DeclarationSpecifier::TypeSpecifier(Type::Int)),
        declarator: Some(Declarator::Identifier{ name: "depth".to_string() }),
      });
      with_depth.append(&mut params.clone());
      with_depth
    };
    let max_depth = self.grammar_depth as i32;
    let prepend_depth_arg = |args: &Vec<Expression>| {
      let mut with_depth = vec!(Expression::ConstInt(max_depth));
      with_depth.append(&mut args.clone());
      with_depth
    };

    // Parameters corresponding to in-scope variables.
    let scope_params = self.in_scope_params();

    // Arguments to in-scope parameters.
    let scope_args = self.in_scope_args();

    // Choice functions, choice variables, and generators.
    let mut choice_vars = Vec::new();
    let mut choice_decls = Vec::new();
    let mut choice_var_mapping = HashMap::new();
    for orig_choice_var in &espec.choice_vars {
      let choice_var = format!("{}_{}", orig_choice_var, self.next_id());
      let choice_fun_name = format!("choice_{}", choice_var);
      let choice_gen_name = format!("gen_choice_{}", choice_var);
      choice_vars.push(choice_var.clone());
      choice_var_mapping.insert(orig_choice_var, choice_var.clone());

      choice_decls.push(BlockItem::Declaration(Declaration {
        specifiers: vec!(DeclarationSpecifier::TypeSpecifier(Type::Int)),
        declarator: Declarator::Identifier{name: choice_var.clone()},
        initializer: Some(Initializer::Expression(Expression::Call {
          callee: Box::new(Expression::Identifier{ name: choice_fun_name.clone() }),
          args: scope_args.clone(),
        }))
      }));
      self.added_choice_funs.push(FunDef {
        specifiers: vec!(DeclarationSpecifier::TypeSpecifier(Type::Int)),
        name: choice_fun_name.clone(),
        params: scope_params.clone(),
        body: Statement::Return(Some(Box::new(Expression::Call {
          callee: Box::new(Expression::Identifier{ name: choice_gen_name.clone() }),
          args: prepend_depth_arg(&scope_args),
        }))),
      });
      self.added_choice_gens.push(FunDef {
        specifiers: vec!(DeclarationSpecifier::TypeSpecifier(Type::Int)),
        name: choice_gen_name.clone(),
        params: prepend_depth_param(&scope_params),
        body: Statement::Return(Some(Box::new(Expression::SketchHole))),
      });
    }

    // Havoc function for the return value.
    let havoc = self.make_havoc();
    let call_havoc = Expression::Binop {
      lhs: Box::new(Expression::Identifier{name: assignee_name.clone()}),
      rhs: Box::new(Expression::Call {
        callee: Box::new(Expression::Identifier{name: havoc.name.clone()}),
        args: self.in_scope_args(),
      }),
      op: BinaryOp::Assign,
    };

    // Pre and post conditions.
    let mut cond_var_mapping = HashMap::new();
    for (param, arg) in espec.params.iter().zip(args) {
      cond_var_mapping.insert(param.name().clone(), arg.clone());
    }
    let assert_pre = spec_cond_to_expression(&espec.pre, &assignee_name, StatementKind::Assert)
      .map_vars(&|name| choice_var_mapping.get(&name).unwrap_or(&name).clone())
      .map(&mut ReplaceIdentifiers::new(cond_var_mapping.clone()));
    let assume_post = spec_cond_to_expression(&espec.post, &assignee_name, StatementKind::Assume)
      .map_vars(&|name| choice_var_mapping.get(&name).unwrap_or(&name).clone())
      .map(&mut ReplaceIdentifiers::new(cond_var_mapping));

    // Putting it all together.
    let mut statements = Vec::new();
    statements.append(&mut choice_decls);
    statements.push(BlockItem::Statement(assert_pre));
    statements.push(BlockItem::Statement(Statement::Expression(Box::new(call_havoc))));
    statements.push(BlockItem::Statement(assume_post));
    Expression::Statement(Box::new(Statement::Compound(statements)))
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

struct ReplaceIdentifiers {
  replacements: HashMap<String, Expression>,
}

impl ReplaceIdentifiers {
  pub fn new(replacements: HashMap<String, Expression>) -> Self {
    ReplaceIdentifiers {
      replacements
    }
  }
}

impl CRelMapper for ReplaceIdentifiers {
  fn map_expression(&mut self, expr: &Expression) -> Expression {
    match expr {
      Expression::Identifier{ name } => match self.replacements.get(name) {
        Some(replacement) => replacement.clone(),
        _ => expr.clone(),
      }
      _ => expr.clone(),
    }
  }
}
