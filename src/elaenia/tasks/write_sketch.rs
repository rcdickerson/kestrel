use crate::crel::ast::*;
use crate::crel::fundef::*;
use crate::escher as Sk;
use crate::spec::to_crel::*;
use crate::elaenia::crel_to_sketch::*;
use crate::elaenia::tasks::elaenia_context::*;
use crate::workflow::context::*;
use crate::workflow::task::*;
use std::collections::HashSet;
use uuid::Uuid;

pub struct WriteSketch {
  add_unrolls: bool,
}

impl WriteSketch {
  pub fn new(add_unrolls: bool) -> Self {
    WriteSketch { add_unrolls }
  }
}

impl Task<ElaeniaContext> for WriteSketch {
  fn name(&self) -> String { "write-sketch".to_string() }

  fn run(&self, context: &mut ElaeniaContext) {
    let crel = context.aligned_crel().as_ref()
      .expect("Missing aligned CRel with forall-exists specifications");
    let (_, fundefs) = crate::crel::fundef::extract_fundefs(crel);
    let main_fun = fundefs.get("main").expect("No main function found");

    let global_decls = context.unaligned_crel().as_ref()
      .expect("Missing unaligned CRel")
      .global_decls.clone();

    let assume_precond = context.precondition_sketch().to_crel(StatementKind::Assume);
    let assert_postcond = context.postcondition().to_crel(StatementKind::Assert);

    let mut new_main_fun = main_fun.body.map(&mut AssertInvars::new());
    if self.add_unrolls {
      let mut unroller = AddUnrolls::new();
      new_main_fun = new_main_fun.map(&mut unroller);
      for unroll in unroller.added_unroll_funs {
        context.accept_unroll_fun(unroll);
      }
    }

    let mut body_items: Vec<BlockItem> = Vec::new();
    body_items.push(BlockItem::Statement(assume_precond));
    body_items.push(BlockItem::Statement(new_main_fun));
    body_items.push(BlockItem::Statement(assert_postcond));
    let new_body = Statement::Compound(body_items);

    let mut sketch = Sk::Source::new();
    for decl in global_decls {
      sketch.declare_variable(&declaration_to_sketch(&decl));
    }
    for havoc_decl in context.havoc_funs_as_decls() {
      sketch.declare_variable(&declaration_to_sketch(&havoc_decl));
    }
    for (aexp_gen, bexp_gen) in context.choice_gens() {
      // AExp LHS generator.
      let aexp_lhs_gen_name = format!("{}_lhs", aexp_gen.name);
      let mut aexp_lhs_gen_fun = fun_to_sketch(
        &aexp_gen.specifiers,
        &aexp_lhs_gen_name,
        &aexp_gen.params,
        &aexp_gen.body);
      aexp_lhs_gen_fun.set_body(&Sk::Statement::Seq(vec!(
        Sk::Statement::Assert(Box::new(Sk::Expression::BinOp {
          lhs: Box::new(Sk::Expression::Identifier{name: "depth".to_string()}),
          rhs: Box::new(Sk::Expression::ConstInt(0)),
          op: ">".to_string(),
        })),
        build_aexp_lhs_grammar(aexp_lhs_gen_fun.get_params()))));
      aexp_lhs_gen_fun.set_generator(true);
      sketch.push_function(&aexp_lhs_gen_fun);

      // AExp generator.
      let mut aexp_gen_fun = fun_to_sketch(
        &aexp_gen.specifiers,
        &aexp_gen.name,
        &aexp_gen.params,
        &aexp_gen.body);
      aexp_gen_fun.set_body(&Sk::Statement::Seq(vec!(
        Sk::Statement::Assert(Box::new(Sk::Expression::BinOp {
          lhs: Box::new(Sk::Expression::Identifier{name: "depth".to_string()}),
          rhs: Box::new(Sk::Expression::ConstInt(0)),
          op: ">".to_string(),
        })),
        build_aexp_grammar(&aexp_gen.name,
                           &aexp_lhs_gen_name,
                           &bexp_gen.name,
                           aexp_gen_fun.get_params()))));
      aexp_gen_fun.set_generator(true);
      sketch.push_function(&aexp_gen_fun);

      // BExp LHS generator.
      let bexp_lhs_gen_name = format!("{}_lhs", bexp_gen.name);
      let mut bexp_lhs_gen_fun = fun_to_sketch(
        &bexp_gen.specifiers,
        &bexp_lhs_gen_name,
        &bexp_gen.params,
        &bexp_gen.body);
      bexp_lhs_gen_fun.set_body(&Sk::Statement::Seq(vec!(
        Sk::Statement::Assert(Box::new(Sk::Expression::BinOp {
          lhs: Box::new(Sk::Expression::Identifier{name: "depth".to_string()}),
          rhs: Box::new(Sk::Expression::ConstInt(0)),
          op: ">".to_string(),
        })),
        build_bexp_lhs_grammar(&aexp_gen.name, bexp_lhs_gen_fun.get_params()))));
      bexp_lhs_gen_fun.set_generator(true);
      sketch.push_function(&bexp_lhs_gen_fun);

      // BExp generator.
      let mut bexp_gen_fun = fun_to_sketch(
        &bexp_gen.specifiers,
        &bexp_gen.name,
        &bexp_gen.params,
        &bexp_gen.body);
      bexp_gen_fun.set_body(&Sk::Statement::Seq(vec!(
        Sk::Statement::Assert(Box::new(Sk::Expression::BinOp {
          lhs: Box::new(Sk::Expression::Identifier{name: "depth".to_string()}),
          rhs: Box::new(Sk::Expression::ConstInt(0)),
          op: ">".to_string(),
        })),
        build_bexp_grammar(&bexp_gen.name, &bexp_lhs_gen_name, bexp_gen_fun.get_params()))));
      bexp_gen_fun.set_generator(true);
      sketch.push_function(&bexp_gen_fun);
    }
    for choice_fun in context.choice_funs() {
      sketch.push_function(&fun_to_sketch(
        &choice_fun.specifiers,
        &choice_fun.name,
        &choice_fun.params,
        &choice_fun.body));
    }
    for unroll_fun in context.unroll_funs() {
      sketch.push_function(&fun_to_sketch(
        &unroll_fun.specifiers,
        &unroll_fun.name,
        &unroll_fun.params,
        &unroll_fun.body));
    }
    let mut main_harness = fun_to_sketch(
      &vec!(DeclarationSpecifier::TypeSpecifier(Type::Void)),
      &"main".to_string(),
      &main_fun.params.clone(),
      &new_body);
    main_harness.set_harness(true);
    sketch.push_function(&main_harness);

    context.accept_sketch_output(sketch.to_string());
  }
}

struct AddUnrolls {
  added_unroll_funs: Vec<FunDef>,
  handled_ids: HashSet<Uuid>,
}

impl AddUnrolls {
  fn new() -> Self {
    AddUnrolls {
      added_unroll_funs: Vec::new(),
      handled_ids: HashSet::new(),
    }
  }

  fn declare_counter(&self, name: &String) -> Declaration {
    Declaration {
      specifiers: vec!(DeclarationSpecifier::TypeSpecifier(Type::Int)),
      declarator: Declarator::Identifier{name: name.clone()},
      initializer: Some(Initializer::Expression(Expression::ConstInt(0))),
    }
  }

  fn declare_unroll(&self, name: &String, choice_fn_name: &String) -> Declaration {
    Declaration {
      specifiers: vec!(DeclarationSpecifier::TypeSpecifier(Type::Int)),
      declarator: Declarator::Identifier{name: name.clone()},
      initializer: Some(Initializer::Expression(
        Expression::Call {
          callee: Box::new(Expression::Identifier{name: choice_fn_name.clone()}),
          args: Vec::new(),
        }
      )),
    }
  }

  fn unroll_loop(&self,
                 body: &Option<Box<Statement>>,
                 condition: &Box<Expression>,
                 unrolls_name: &String,
                 unrolls_choice_fn_name: &String,
                 counter_name: &String) -> Statement {
    match body {
      None => Statement::None,
      Some(body) => {
        let unrolls_decl = self.declare_unroll(unrolls_name, unrolls_choice_fn_name);
        let counter_decl = self.declare_counter(counter_name);
        Statement::Compound(vec!(
          BlockItem::Declaration(unrolls_decl),
          BlockItem::Statement(Statement::Assert(Box::new(
            Expression::Binop {
              lhs: Box::new(Expression::Identifier{ name: unrolls_name.clone() }),
              rhs: Box::new(Expression::ConstInt(0)),
              op: BinaryOp::Gte,
            }
          ))),
          BlockItem::Statement(Statement::Assert(Box::new(
            Expression::Binop {
              lhs: Box::new(Expression::Identifier{ name: unrolls_name.clone() }),
              rhs: Box::new(Expression::ConstInt(5)),
              op: BinaryOp::Lte,
            }
          ))),
          BlockItem::Declaration(counter_decl),
          BlockItem::Statement(Statement::While {
            id: Uuid::new_v4(),
            invariants: Vec::new(),
            is_merged: false,
            is_runoff: false,
            runoff_link_id: None,
            condition: Box::new(Expression::Binop {
              lhs: Box::new(Expression::Identifier{name: counter_name.clone()}),
              rhs: Box::new(Expression::Identifier{name: unrolls_name.clone()}),
              op: BinaryOp::Lt,
            }),
            body: Some(Box::new(Statement::Compound(vec!(
              BlockItem::Statement(Statement::If {
                condition: condition.clone(),
                then: body.clone(),
                els: None,
              }),
              BlockItem::Statement(Statement::Expression(Box::new(Expression::Binop {
                lhs: Box::new(Expression::Identifier{name: counter_name.clone()}),
                rhs: Box::new(Expression::Binop {
                  lhs: Box::new(Expression::Identifier{name: counter_name.clone()}),
                  rhs: Box::new(Expression::ConstInt(1)),
                  op: BinaryOp::Add,
                }),
                op: BinaryOp::Assign,
              })),
              ))
            ))),
          }),
        ))
      }
    }
  }
}

impl crate::crel::mapper::CRelMapper for AddUnrolls {
  fn map_statement(&mut self, stmt: &Statement) -> Statement {
    match stmt {
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

        if self.handled_ids.contains(id) {
          return stmt.clone();
        }

        let unrolls_name_l = format!("_{}_l", id).replace("-", "");
        let unrolls_choice_name_l = format!("unroll{}", unrolls_name_l);
        let counter_name_l = format!("_{}_li", id).replace("-", "");
        let unrolls_left = self.unroll_loop(&body_left, condition_left,
                                       &unrolls_name_l, &unrolls_choice_name_l,
                                       &counter_name_l);

        let unrolls_name_r = format!("_{}_r", id).replace("-", "");
        let unrolls_choice_name_r = format!("unroll{}", unrolls_name_r);
        let counter_name_r = format!("_{}_ri", id).replace("-", "");
        let unrolls_right = self.unroll_loop(&body_right, condition_right,
                                        &unrolls_name_r, &unrolls_choice_name_r,
                                        &counter_name_r);

        self.added_unroll_funs.push(FunDef {
          specifiers: vec!(DeclarationSpecifier::TypeSpecifier(Type::Int)),
          name: unrolls_choice_name_l.clone(),
          params: Vec::new(),
          body: Statement::Return(Some(Box::new(Expression::SketchHole))),
        });
        self.added_unroll_funs.push(FunDef {
          specifiers: vec!(DeclarationSpecifier::TypeSpecifier(Type::Int)),
          name: unrolls_choice_name_r.clone(),
          params: Vec::new(),
          body: Statement::Return(Some(Box::new(Expression::SketchHole))),
        });

        Statement::Compound(vec!(
          BlockItem::Statement(unrolls_left),
          BlockItem::Statement(unrolls_right),
          BlockItem::Statement(Statement::WhileRel {
            id: id.clone(),
            unroll_left: *unroll_left,
            unroll_right: *unroll_right,
            stutter_left: *stutter_left,
            stutter_right: *stutter_right,
            invariants_left: invariants_left.clone(),
            invariants_right: invariants_right.clone(),
            condition_left: condition_left.clone(),
            condition_right: condition_right.clone(),
            body_left: body_left.clone(),
            body_right: body_right.clone(),
            body_merged: body_merged.clone(),
          }),
        ))
      },
      _ => stmt.clone(),
    }
  }
}

struct AssertInvars {}
impl AssertInvars {
  fn new() -> Self {
    AssertInvars {}
  }
}
impl crate::crel::mapper::CRelMapper for AssertInvars {
  fn map_statement(&mut self, stmt: &Statement) -> Statement {
    match stmt {
      Statement::While { id,
                         runoff_link_id,
                         invariants,
                         condition,
                         body,
                         is_runoff,
                         is_merged } => {
        let body_with_invars = body.as_ref().map(|some_body| {
          let mut new_body = invariants.into_iter()
            .map(|invar| {
              BlockItem::Statement(Statement::Assert(Box::new(invar.clone())))
            })
            .collect::<Vec<_>>();
          new_body.push(BlockItem::Statement(*some_body.clone()));
          Box::new(Statement::Compound(new_body))
        });
        Statement::While {
          id: id.clone(),
          runoff_link_id: runoff_link_id.clone(),
          invariants: invariants.clone(),
          condition: condition.clone(),
          body: body_with_invars,
          is_runoff: is_runoff.clone(),
          is_merged: is_merged.clone(),
        }
      },
      _ => stmt.clone()
    }
  }
}

fn build_aexp_lhs_grammar(params: &Vec<Sk::FunctionParameter>)
                          -> Sk::Statement {
  let mut options = vec!(
    Sk::Expression::Hole,
  );
  for param in params {
    match &param.name {
      Some(name) if name.as_str() == "depth" => (),
      _ => if !param.is_array {
          options.push(Sk::Expression::Identifier {
            name: param.name.clone().expect("Encountered nameless parameter")
          });
        }
    }
  }
  Sk::Statement::Return(Some(Box::new(Sk::Expression::GeneratorOptions(options))))
}

fn build_aexp_grammar(aexp_generator_name: &String,
                      aexp_lhs_generator_name: &String,
                      bexp_generator_name: &String,
                      params: &Vec<Sk::FunctionParameter>)
                      -> Sk::Statement {
  let sk_params = |depth_dec: i32| {
    params.into_iter()
      .map(|p| match &p.name {
        Some(name) if name.as_str() == "depth" =>
          match depth_dec {
            0 => Sk::Expression::Identifier{ name: name.clone() },
            _ => Sk::Expression::BinOp {
              lhs: Box::new(Sk::Expression::Identifier{ name: name.clone() }),
              rhs: Box::new(Sk::Expression::ConstInt(1)),
              op: "-".to_string(),
            },
          }
        _ => Sk::Expression::Identifier {
          name: p.name.clone().expect("Encountered nameless parameter")
        },
      })
    .collect::<Vec<_>>()
  };
  let aexp_lhs = Sk::Expression::FnCall {
    name: Box::new(Sk::Expression::Identifier{name: aexp_lhs_generator_name.clone()}),
    args: sk_params(0),
  };
  let recurse_aexp = Sk::Expression::FnCall {
    name: Box::new(Sk::Expression::Identifier{name: aexp_generator_name.clone()}),
    args: sk_params(1),
  };
  let recurse_bexp = Sk::Expression::FnCall {
    name: Box::new(Sk::Expression::Identifier{name: bexp_generator_name.clone()}),
    args: sk_params(1),
  };

  let mut options = vec!(
    Sk::Expression::Hole,
  );
  options.push(aexp_lhs.clone());
  options.push(Sk::Expression::BinOp {
    lhs: Box::new(aexp_lhs.clone()),
    rhs: Box::new(recurse_aexp.clone()),
    op: "+".to_string(),
  });
  options.push(Sk::Expression::BinOp {
    lhs: Box::new(aexp_lhs.clone()),
    rhs: Box::new(recurse_aexp.clone()),
    op: "*".to_string(),
  });
  options.push(Sk::Expression::BinOp {
    lhs: Box::new(recurse_aexp.clone()),
    rhs: Box::new(recurse_aexp.clone()),
    op: "-".to_string(),
  });
  options.push(Sk::Expression::Ternary {
    condition: Box::new(recurse_bexp.clone()),
    then: Box::new(recurse_aexp.clone()),
    els: Box::new(recurse_aexp.clone()),
  });
  Sk::Statement::Return(Some(Box::new(Sk::Expression::GeneratorOptions(options))))
}

fn build_bexp_lhs_grammar(aexp_generator_name: &String,
                          params: &Vec<Sk::FunctionParameter>)
                          -> Sk::Statement {
  let sk_params = params.into_iter()
    .map(|p| match &p.name {
      Some(name) if name.as_str() == "depth" => Sk::Expression::BinOp {
        lhs: Box::new(Sk::Expression::Identifier{ name: name.clone() }),
        rhs: Box::new(Sk::Expression::ConstInt(1)),
        op: "-".to_string(),
      },
      _ => Sk::Expression::Identifier {
        name: p.name.clone().expect("Encountered nameless parameter")
      },
    })
    .collect::<Vec<_>>();
  let recurse_aexp = Sk::Expression::FnCall {
    name: Box::new(Sk::Expression::Identifier{name: aexp_generator_name.clone()}),
    args: sk_params.clone(),
  };
  let mut options = Vec::new();
  options.push(Sk::Expression::BinOp {
    lhs: Box::new(recurse_aexp.clone()),
    rhs: Box::new(recurse_aexp.clone()),
    op: "==".to_string(),
  });
  options.push(Sk::Expression::BinOp {
    lhs: Box::new(recurse_aexp.clone()),
    rhs: Box::new(recurse_aexp.clone()),
    op: "<=".to_string(),
  });
  options.push(Sk::Expression::BinOp {
    lhs: Box::new(recurse_aexp.clone()),
    rhs: Box::new(recurse_aexp.clone()),
    op: ">=".to_string(),
  });
  Sk::Statement::Return(Some(Box::new(Sk::Expression::GeneratorOptions(options))))
}

fn build_bexp_grammar(bexp_generator_name: &String,
                      bexp_lhs_generator_name: &String,
                      params: &Vec<Sk::FunctionParameter>)
                      -> Sk::Statement {
  let sk_params = |depth_dec: i32| {
    params.into_iter()
      .map(|p| match &p.name {
        Some(name) if name.as_str() == "depth" =>
          match depth_dec {
            0 => Sk::Expression::Identifier{ name: name.clone() },
            _ => Sk::Expression::BinOp {
              lhs: Box::new(Sk::Expression::Identifier{ name: name.clone() }),
              rhs: Box::new(Sk::Expression::ConstInt(1)),
              op: "-".to_string(),
            },
          }
        _ => Sk::Expression::Identifier {
          name: p.name.clone().expect("Encountered nameless parameter")
        },
      })
    .collect::<Vec<_>>()
  };
  let bexp_lhs = Sk::Expression::FnCall {
    name: Box::new(Sk::Expression::Identifier{name: bexp_lhs_generator_name.clone()}),
    args: sk_params(0),
  };
  let recurse_bexp = Sk::Expression::FnCall {
    name: Box::new(Sk::Expression::Identifier{name: bexp_generator_name.clone()}),
    args: sk_params(1),
  };

  let mut options = Vec::new();
  options.push(bexp_lhs.clone());
  options.push(Sk::Expression::BinOp {
    lhs: Box::new(bexp_lhs.clone()),
    rhs: Box::new(recurse_bexp.clone()),
    op: "&&".to_string(),
  });
  options.push(Sk::Expression::UnOp {
    expr: Box::new(recurse_bexp.clone()),
    op: "!".to_string(),
  });
  Sk::Statement::Return(Some(Box::new(Sk::Expression::GeneratorOptions(options))))
}
