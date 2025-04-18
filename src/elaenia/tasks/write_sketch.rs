use crate::crel::ast::*;
use crate::escher as Sk;
use crate::spec::to_crel::*;
use crate::elaenia::crel_to_sketch::*;
use crate::elaenia::tasks::elaenia_context::*;
use crate::workflow::context::*;
use crate::workflow::task::*;

pub struct WriteSketch { }

impl WriteSketch {
  pub fn new() -> Self {
    WriteSketch { }
  }
}

impl Task<ElaeniaContext> for WriteSketch {
  fn name(&self) -> String { "write-sketch".to_string() }

  fn run(&self, context: &mut ElaeniaContext) {
    let crel = context.aligned_crel().as_ref().expect("Missing aligned CRel");
    let (_, fundefs) = crate::crel::fundef::extract_fundefs(crel);
    let main_fun = fundefs.get("main").expect("No main function found");

    let global_decls = &context.unaligned_crel().as_ref()
      .expect("Missing unaligned CRel")
      .global_decls;

    let assume_precond = context.spec().pre.to_crel(StatementKind::Assume);
    let assert_postcond = context.spec().post.to_crel(StatementKind::Assert);

    let mut body_items: Vec<BlockItem> = Vec::new();
    body_items.push(BlockItem::Statement(assume_precond));
    body_items.push(BlockItem::Statement(main_fun.body
                                         .map(&mut AssertInvars::new())));
    body_items.push(BlockItem::Statement(assert_postcond));
    let new_body = Statement::Compound(body_items);

    let mut sketch = Sk::Source::new();
    for decl in global_decls {
      sketch.declare_variable(&declaration_to_sketch(decl));
    }
    for choice_gen in context.choice_gens() {
      let mut fun = fun_to_sketch(
        &choice_gen.specifiers,
        &choice_gen.name,
        &choice_gen.params,
        &choice_gen.body);
      fun.set_body(&Sk::Statement::Seq(vec!(
        Sk::Statement::Assert(Box::new(Sk::Expression::BinOp {
          lhs: Box::new(Sk::Expression::Identifier{name: "depth".to_string()}),
          rhs: Box::new(Sk::Expression::ConstInt(0)),
          op: ">".to_string(),
        })),
        build_grammar(&choice_gen.name, fun.get_params()))));
      fun.set_generator(true);
      sketch.push_function(&fun);
    }
    for choice_fun in context.choice_funs() {
      sketch.push_function(&fun_to_sketch(
        &choice_fun.specifiers,
        &choice_fun.name,
        &choice_fun.params,
        &choice_fun.body));
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

fn build_grammar(generator_name: &String,
                 params: &Vec<Sk::FunctionParameter>)
                 -> Sk::Statement {
  let mut options = vec!(
    Sk::Expression::Hole,
  );
  for param in params {
    match &param.name {
      Some(name) if name.as_str() == "depth" => (),
      _ => {
        options.push(Sk::Expression::Identifier {
          name: param.name.clone().expect("Encountered nameless parameter")
        });
      }
    }
  }
  let recurse = Sk::Expression::FnCall {
    name: Box::new(Sk::Expression::Identifier{name: generator_name.clone()}),
    args: params.into_iter()
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
      .collect(),
  };
  options.push(Sk::Expression::BinOp {
    lhs: Box::new(recurse.clone()),
    rhs: Box::new(recurse.clone()),
    op: "+".to_string(),
  });
  options.push(Sk::Expression::BinOp {
    lhs: Box::new(recurse.clone()),
    rhs: Box::new(recurse.clone()),
    op: "-".to_string(),
  });
  options.push(Sk::Expression::BinOp {
    lhs: Box::new(recurse.clone()),
    rhs: Box::new(recurse.clone()),
    op: "*".to_string(),
  });
  options.push(Sk::Expression::Ternary {
    condition: Box::new(Sk::Expression::BinOp {
      lhs: Box::new(recurse.clone()),
      rhs: Box::new(recurse.clone()),
      op: "<".to_string(),
    }),
    then: Box::new(recurse.clone()),
    els: Box::new(recurse.clone()),
  });
  Sk::Statement::Return(Some(Box::new(Sk::Expression::GeneratorOptions(options))))
}
