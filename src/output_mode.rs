use clap::ValueEnum;
use crate::crel::ast::*;
use crate::spec::{*, to_crel::*};

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
pub enum OutputMode {
  Seahorn,
  SvComp,
}

impl OutputMode {
  pub fn prepare_crel(&self,
                      crel: &CRel,
                      spec: &KestrelSpec,
                      global_decls: Vec<Declaration>,
                      filename: &Option<String>) -> String {
    let top = match self {
      OutputMode::Seahorn => seahorn_top().to_string(),
      OutputMode::SvComp => svcomp_top(filename),
    };
    let (_, fundefs) = crate::crel::fundef::extract_fundefs(crel);
    let main_fun = fundefs.get("main").expect("No main function found");

    let mut arb_inits = build_param_inits(&main_fun.params);
    let preconds = BlockItem::Statement(spec.pre.to_crel(StatementKind::Assume));
    let postconds = BlockItem::Statement(spec.post.to_crel(StatementKind::Assert));

    let mut body_items: Vec<BlockItem> = Vec::new();
    body_items.append(&mut arb_inits);
    body_items.push(preconds);
    body_items.push(BlockItem::Statement(main_fun.body.clone()));
    body_items.push(postconds);
    let new_body = Statement::Compound(body_items);

    let new_main = CRel::FunctionDefinition {
      specifiers: vec!(DeclarationSpecifier::TypeSpecifier(Type::Void)),
      name: "main".to_string(),
      params: Vec::new(),
      body: Box::new(new_body),
    };

    let mut new_seq: Vec<CRel> = global_decls.iter()
      .map(|decl| CRel::Declaration(decl.clone()))
      .collect();
    new_seq.push(new_main);
    format!("{}\n{}", top, CRel::Seq(new_seq).to_c())
  }
}

fn seahorn_top<'a>() -> &'a str {
"#include \"seahorn/seahorn.h\"\n
extern int arb_int();\n"
}

fn svcomp_top(filename: &Option<String>) -> String {
format!("extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() {{ __assert_fail(\"0\", \"{}\", 3, \"reach_error\"); }}

void sassert(int cond) {{
  if (!(cond)) {{
    ERROR: {{reach_error();abort();}}
  }}
  return;
}}
void assume(int cond) {{
  if(!cond) {{abort();}}
}}

int arb_int();\n", filename.as_ref().unwrap_or(&"anonymous".to_string()))
}

fn build_param_inits(params: &Vec<ParameterDeclaration>) -> Vec<BlockItem> {
  let call_arb_int = Expression::Call {
    callee: Box::new(Expression::Identifier{name: "arb_int".to_string()}),
    args: Vec::new(),
  };
  params.iter()
    .filter(|param| param.declarator.is_some())
    .map(|param| {
      let c_param = param.to_c();
      let is_int = c_param.ty == crate::shanty::Type::Int;
      let is_array = c_param.is_array;
      let is_ptr = c_param.is_pointer;
      let initializer = if is_int && !is_array && !is_ptr {
        Some(call_arb_int.clone())
      } else {
        None
      };
      BlockItem::Declaration(
        Declaration {
          specifiers: param.specifiers.clone(),
          declarator: param.declarator.as_ref().unwrap().clone(),
          initializer
        }
      )
    })
    .collect()
}
