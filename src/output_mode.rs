use clap::ValueEnum;
use crate::crel::ast::*;
use crate::spec::{*, to_crel::*};

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
pub enum OutputMode {
  /*TODO: Dafny*/
  Daikon,
  Icra,
  Seahorn,
  SvComp,
}

pub struct Options {
  pub assert_name: Option<String>,
  pub assume_name: Option<String>,
  pub nondet_name: Option<String>,
}

impl OutputMode {
  pub fn crel_to_c(&self,
                   crel: &CRel,
                   spec: &KestrelSpec,
                   global_decls: Vec<Declaration>,
                   filename: &Option<String>) -> String {
    let options = self.options();
    let (_, fundefs) = crate::crel::fundef::extract_fundefs(crel);
    let main_fun = fundefs.get("main").expect("No main function found");

    let param_inits = self.build_param_inits(&main_fun.params);
    let preconds = options.assume_name.map(|name| {
      BlockItem::Statement(spec.pre.to_crel(StatementKind{crel_name: name}))
    });
    let postconds = options.assert_name.map(|name| {
      BlockItem::Statement(spec.post.to_crel(StatementKind{crel_name: name}))
    });

    let mut body_items: Vec<BlockItem> = Vec::new();
    param_inits.clone().map(|mut param_inits| body_items.append(&mut param_inits));
    preconds.map(|preconds| body_items.push(preconds));
    body_items.push(BlockItem::Statement(main_fun.body.clone()));
    postconds.map(|postconds| body_items.push(postconds));
    let new_body = Statement::Compound(body_items);

    let new_main = CRel::FunctionDefinition {
      specifiers: vec!(DeclarationSpecifier::TypeSpecifier(Type::Void)),
      name: "main".to_string(),
      params: match param_inits {
        None => main_fun.params.clone(),
        Some(_) => Vec::new(),
      },
      body: Box::new(new_body),
    };

    let mut new_seq: Vec<CRel> = global_decls.iter()
      .map(|decl| CRel::Declaration(decl.clone()))
      .collect();
    new_seq.push(new_main);
    format!("{}\n{}", self.top(filename), CRel::Seq(new_seq).to_c())
  }

  fn top(&self, filename: &Option<String>) -> String {
    match self {
      OutputMode::Daikon => {
        "#include \"assert.h\"".to_string()
      }
      OutputMode::Icra => {
        "#include \"assert.h\"".to_string()
      }
      OutputMode::Seahorn => {
        [
          "#include \"seahorn/seahorn.h\"",
          "extern int arb_int();"
        ].join("\n")
      },
      OutputMode::SvComp => {
        [
          "extern void abort(void);",
          "extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));",
          format!("void reach_error() {{ __assert_fail(\"0\", \"{}\", 3, \"reach_error\"); }}",
                  filename.as_ref().unwrap_or(&"anonymous".to_string())).as_str(),
          "",
          "void sassert(int cond) {{",
          "  if (!(cond)) {{",
          "    ERROR: {{reach_error();abort();}}",
          "  }}",
          "  return;",
          "}}",
          "void assume(int cond) {{",
          "  if(!cond) {{abort();}}",
          "}}",
          "",
          "int arb_int();"
        ].join("\n")
      },
    }
  }

  pub fn options(&self) -> Options {
    match self {
      OutputMode::Daikon => {
        Options {
          assert_name: None,
          assume_name: None,
          nondet_name: None,
        }
      },
      OutputMode::Icra => {
        Options {
          assert_name: Some("__VERIFIER_assert".to_string()),
          assume_name: Some("__VERIFIER_assume".to_string()),
          nondet_name: Some("nondet".to_string()),
        }
      },
      OutputMode::Seahorn => {
        Options {
          assert_name: Some("sassert".to_string()),
          assume_name: Some("assume".to_string()),
          nondet_name: Some("arb_int".to_string()),
        }
      },
      OutputMode::SvComp => {
        Options {
          assert_name: Some("sassert".to_string()),
          assume_name: Some("assume".to_string()),
          nondet_name: Some("arb_int".to_string()),
        }
      },
    }
  }

  fn build_param_inits(&self, params: &Vec<ParameterDeclaration>) -> Option<Vec<BlockItem>> {
    let options = self.options();
    let nondet_name = options.nondet_name?;
    let call_nondet_int = Expression::Call {
      callee: Box::new(Expression::Identifier{name: nondet_name}),
      args: Vec::new(),
    };
    Some(params.iter()
      .filter(|param| param.declarator.is_some())
      .map(|param| {
        let c_param = param.to_c();
        let is_int = c_param.ty == crate::shanty::Type::Int;
        let is_array = c_param.is_array;
        let is_ptr = c_param.is_pointer;
        let initializer = if is_int && !is_array && !is_ptr {
          Some(call_nondet_int.clone())
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
      .collect())
  }
}
