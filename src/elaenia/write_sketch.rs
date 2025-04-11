use crate::crel::ast::*;
use crate::escher as Sk;
use crate::spec::to_crel::*;
use crate::elaenia::crel_to_sketch::*;
use crate::elaenia::elaenia_context::*;
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
    body_items.push(BlockItem::Statement(main_fun.body.clone()));
    body_items.push(BlockItem::Statement(assert_postcond));
    let new_body = Statement::Compound(body_items);

    let mut sketch = Sk::Source::new();
    for decl in global_decls {
      sketch.declare_variable(&declaration_to_sketch(decl));
    }
    for choice_gen in context.choice_gens() {
      sketch.push_function(&fun_to_sketch(
        &choice_gen.specifiers,
        &choice_gen.name,
        &choice_gen.params,
        &choice_gen.body).set_generator(true));
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
