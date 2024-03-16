use clap::ValueEnum;
use crate::crel::ast::*;
use crate::crel::daikon_converter::*;
use crate::crel::fundef::*;
use crate::eggroll::to_crel;
use crate::spec::{*, to_crel::*};
use rand::Rng;
use std::collections::HashMap;

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
pub enum OutputMode {
  Daikon,
  Dafny,
  Icra,
  Seahorn,
  SvComp,
}

impl OutputMode {

  pub fn crel_to_output(&self,
                        crel: &CRel,
                        spec: &KestrelSpec,
                        global_decls: Vec<Declaration>,
                        fundefs: HashMap<String, FunDef>,
                        filename: &Option<String>) -> String {
    match self {
      // TODO: Refactor these crel_to_* methods to exploit commonalities.
      OutputMode::Dafny => self.crel_to_dafny(&crel, spec, global_decls, filename).0,
      OutputMode::Daikon => self.crel_to_daikon(&crel, global_decls, fundefs, filename),
      _ => self.crel_to_c(&crel, spec, global_decls, filename),
    }
  }

  pub fn crel_to_dafny(&self,
                       crel: &CRel,
                       spec: &KestrelSpec,
                       global_decls: Vec<Declaration>,
                       filename: &Option<String>) -> (String, HashMap<String, (usize, usize)>) {
    let (_, fundefs) = crate::crel::fundef::extract_fundefs(crel);
    let main_fun = fundefs.get("main").expect("No main function found");

    let preconds = self.assume_name().map(|name| {
      BlockItem::Statement(spec.pre.to_crel(StatementKind{crel_name: name}))
    });
    let postconds = self.assert_name().map(|name| {
      BlockItem::Statement(spec.post.to_crel(StatementKind{crel_name: name}))
    });

    let globals = global_decls.iter()
      .map(|decl| CRel::Declaration(decl.clone()).to_dafny().0)
      .collect::<Vec<String>>()
      .join("");

    let mut body_items: Vec<BlockItem> = Vec::new();
    if let Some(preconds) = preconds { body_items.push(preconds) }
    body_items.push(BlockItem::Statement(main_fun.body.clone()));
    if let Some(postconds) = postconds { body_items.push(postconds) }
    let new_body = Statement::Compound(body_items);

    let new_main = CRel::FunctionDefinition {
      specifiers: vec!(DeclarationSpecifier::TypeSpecifier(Type::Void)),
      name: "Main".to_string(),
      params: main_fun.params.clone(),
      body: Box::new(new_body),
    };
    let (dafny_output, while_lines) = new_main.to_dafny();
    let topmatter = format!("{}{}", globals, self.top(filename));
    let while_lines = while_lines.iter()
      .map(|(id, (start, end))| (id.clone(), (start + topmatter.lines().count() + 1,
                                              end   + topmatter.lines().count() + 1)))
      .collect::<HashMap<_, _>>();
    (format!("{}{}", topmatter, dafny_output), while_lines)
  }

  pub fn crel_to_daikon(&self,
                        crel: &CRel,
                        global_decls: Vec<Declaration>,
                        fundefs: HashMap<String, FunDef>,
                        filename: &Option<String>) -> String {

    const TEST_GEN_FUN_NAME: &str = "_test_gen";

    let (_, crel_fundefs) = crate::crel::fundef::extract_fundefs(crel);
    let main_fun = crel_fundefs.get("main").expect("No main function found");
    let (daikon_body, loop_head_funs) = DaikonConverter::new(main_fun.body.clone()).convert();

    let new_main = CRel::FunctionDefinition {
      specifiers: vec!(DeclarationSpecifier::TypeSpecifier(Type::Void)),
      name: "_main".to_string(),
      params: main_fun.params.clone(),
      body: Box::new(daikon_body),
    };

    let mut rng = rand::thread_rng();
    let mut test_cases = Vec::new();
    let (test_fun_name, test_fun) = match fundefs.get(TEST_GEN_FUN_NAME) {
      Option::None => ("_main", main_fun),
      Option::Some(f) => (TEST_GEN_FUN_NAME, f),
    };
    for _ in 0..20 {
      let mut args = Vec::new();
      for param in &test_fun.params {
        let arg = match param.get_type() {
          None => panic!("Parameter without type in main function."),
          Some(ty) => match ty {
            Type::Bool => Expression::ConstInt(rng.gen_range(0..1)),
            Type::Int => Expression::ConstInt(rng.gen()),
            Type::Float => Expression::ConstFloat(rng.gen()),
            _ => panic!("Unsupported: randomly generated {:?}", ty),
          }
        };
        args.push(arg);
      }
      test_cases.push(BlockItem::Statement(Statement::Expression(Box::new(Expression::Call {
        callee: Box::new(Expression::Identifier{name: test_fun_name.to_string()}),
        args
      }))));
    }

    let driver = CRel::FunctionDefinition {
      specifiers: vec!(DeclarationSpecifier::TypeSpecifier(Type::Int)),
      name: "main".to_string(),
      params: Vec::new(),
      body: Box::new(Statement::Compound(vec![
        BlockItem::Statement(Statement::Compound(test_cases)),
        BlockItem::Statement(Statement::Return(Some(Box::new(Expression::ConstInt(0)))))
      ])),
    };

    let mut new_seq: Vec<CRel> = global_decls.iter()
      .map(|decl| match &decl.declarator {
        Declarator::Function{name, params} => {
          self.daikon_default_fun(&decl.specifiers, name.clone(), params)
        },
        _ => CRel::Declaration(decl.clone()),
      })
      .collect();
    new_seq.push(CRel::Seq(loop_head_funs));
    new_seq.push(new_main);
    fundefs.get(TEST_GEN_FUN_NAME).map(|f| {
      let gen_fun = CRel::FunctionDefinition {
        specifiers: vec!(DeclarationSpecifier::TypeSpecifier(Type::Void)),
        name: TEST_GEN_FUN_NAME.to_string(),
        params: f.params.clone(),
        body: Box::new(f.body.clone()),
      };
      new_seq.push(gen_fun)
    });
    new_seq.push(driver);
    format!("{}\n{}", self.top(filename), CRel::Seq(new_seq).to_c())
  }

  //TODO: Refactor; this function does not belong in the impl of OutputMode.
  fn daikon_default_fun(&self,
                        fun_specifiers: &Vec<DeclarationSpecifier>,
                        fun_name: String,
                        fun_params: &Vec<ParameterDeclaration>) -> CRel {
    let hash_name = "hash".to_string();
    let hash_id: Expression = Expression::Identifier{name: hash_name.clone()};

    let mut body = vec![BlockItem::Declaration(Declaration {
      specifiers: vec![DeclarationSpecifier::TypeSpecifier(Type::Int)],
      declarator: Declarator::Identifier{name: hash_name.clone()},
      initializer: Some(Expression::ConstInt(0)),
    })];

    let mut converted_params = Vec::new();
    let mut param_name_counter = 0;
    for param in fun_params {
      let param_name = match &param.declarator {
        None => {
          let name = format!("_p_{}", param_name_counter);
          converted_params.push(ParameterDeclaration {
            specifiers: param.specifiers.clone(),
            declarator: Some(Declarator::Identifier{name: name.clone()}),
          });
          param_name_counter += 1;
          name
        },
        Some(decl) => match decl {
          Declarator::Identifier{name} => {
            converted_params.push(param.clone());
            name.clone()
          },
          _ => panic!("loop head paramameter declarator not supported: {:?}", decl),
        }
      };
      let updated_hash = Expression::Binop {
        op: BinaryOp::Add,
        lhs: Box::new(Expression::Binop {
          op: BinaryOp::Mul,
          lhs: Box::new(Expression::ConstInt(31)),
          rhs: Box::new(hash_id.clone()),
        }),
        rhs: Box::new(Expression::Identifier{name: param_name}),
      };
      body.push(BlockItem::Statement(Statement::Expression(Box::new(Expression::Binop {
        op: BinaryOp::Assign,
        lhs: Box::new(hash_id.clone()),
        rhs: Box::new(updated_hash),
      }))));
    }
    body.push(BlockItem::Statement(Statement::Return(Some(Box::new(hash_id.clone())))));

    CRel::FunctionDefinition {
      specifiers: fun_specifiers.clone(),
      name: fun_name.clone(),
      params: converted_params,
      body: Box::new(Statement::Compound(body)),
    }
  }

  pub fn crel_to_c(&self,
                   crel: &CRel,
                   spec: &KestrelSpec,
                   global_decls: Vec<Declaration>,
                   filename: &Option<String>) -> String {
    let (_, fundefs) = crate::crel::fundef::extract_fundefs(crel);
    let main_fun = fundefs.get("main").expect("No main function found");

    let param_inits = self.build_param_inits(&main_fun.params);
    let preconds = self.assume_name().map(|name| {
      BlockItem::Statement(spec.pre.to_crel(StatementKind{crel_name: name}))
    });
    let postconds = self.assert_name().map(|name| {
      BlockItem::Statement(spec.post.to_crel(StatementKind{crel_name: name}))
    });

    let mut body_items: Vec<BlockItem> = Vec::new();
    if let Some(mut param_inits) = param_inits.clone() { body_items.append(&mut param_inits) }
    if let Some(preconds) = preconds { body_items.push(preconds) }
    body_items.push(BlockItem::Statement(main_fun.body.clone()));
    if let Some(postconds) = postconds { body_items.push(postconds) }
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
      OutputMode::Dafny => {
        "".to_string()
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

  pub fn crel_config(&self) -> to_crel::Config {
    to_crel::Config {
      assert_name: self.assert_name(),
      assume_name: self.assume_name(),
      nondet_name: self.nondet_name(),
    }
  }

  pub fn assert_name(&self) -> Option<String> {
    match self {
      OutputMode::Daikon => None,
      OutputMode::Dafny => Some("assert".to_string()),
      OutputMode::Icra => Some("__VERIFIER_assert".to_string()),
      OutputMode::Seahorn => Some("sassert".to_string()),
      OutputMode::SvComp => Some("sassert".to_string()),
    }
  }

  pub fn assume_name(&self) -> Option<String> {
    match self {
      OutputMode::Daikon => None,
      OutputMode::Dafny => Some("assume".to_string()),
      OutputMode::Icra => Some("__VERIFIER_assume".to_string()),
      OutputMode::Seahorn => Some("assume".to_string()),
      OutputMode::SvComp => Some("assume".to_string()),
    }
  }

  pub fn nondet_name(&self) -> Option<String> {
    match self {
      OutputMode::Daikon => None,
      OutputMode::Dafny => None,
      OutputMode::Icra => Some("nondet".to_string()),
      OutputMode::Seahorn => Some("arb_int".to_string()),
      OutputMode::SvComp => Some("arb_int".to_string()),
    }
  }

  fn build_param_inits(&self, params: &Vec<ParameterDeclaration>) -> Option<Vec<BlockItem>> {
    let nondet_name = self.nondet_name()?;
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
