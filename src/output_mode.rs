//! Configuration for KestRel's supported output modes.

use clap::ValueEnum;
use crate::crel::ast::*;
use crate::crel::auto_fun_impl::*;
use crate::crel::daikon_converter::*;
use crate::crel::fundef::*;
use crate::eggroll::to_crel;
use crate::spec::condition::KestrelCond;
use crate::spec::to_crel::*;
use rand::Rng;
use std::collections::HashMap;
use uuid::Uuid;

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
                        precond: &KestrelCond,
                        postcond: &KestrelCond,
                        global_decls: Vec<Declaration>,
                        fundefs: HashMap<String, FunDef>,
                        filename: &Option<String>) -> String {
    match self {
      // TODO: Refactor these crel_to_* methods to exploit commonalities.
      OutputMode::Dafny => self.crel_to_dafny(&crel, precond, postcond, global_decls, filename).0,
      OutputMode::Daikon => self.crel_to_daikon(&crel, global_decls, fundefs, filename, None, 20),
      _ => self.crel_to_c(&crel, precond, postcond, global_decls, filename),
    }
  }

  pub fn crel_to_dafny(&self,
                       crel: &CRel,
                       precond: &KestrelCond,
                       postcond: &KestrelCond,
                       global_decls: Vec<Declaration>,
                       filename: &Option<String>) -> (String, HashMap<String, (usize, usize)>) {
    let (_, fundefs) = crate::crel::fundef::extract_fundefs(crel);
    let main_fun = fundefs.get("main").expect("No main function found");

    let preconds  = BlockItem::Statement(precond.to_crel(StatementKind::Assume));
    let postconds = BlockItem::Statement(postcond.to_crel(StatementKind::Assert));

    let globals = global_decls.iter()
      .map(|decl| CRel::Declaration(decl.clone()).to_dafny().0)
      .collect::<Vec<String>>()
      .join("");

    let mut body_items: Vec<BlockItem> = Vec::new();
    body_items.push(preconds);
    body_items.push(BlockItem::Statement(main_fun.body.clone()));
    body_items.push(postconds);
    let new_body = Statement::Compound(body_items);

    let new_main = CRel::FunctionDefinition {
      specifiers: vec!(DeclarationSpecifier::TypeSpecifier(Type::Void)),
      name: "Product".to_string(),
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

  // TODO: This is hacked together raw CRel encodings when it should be
  // something nicer.
  pub fn crel_to_daikon(&self,
                        crel: &CRel,
                        global_decls: Vec<Declaration>,
                        fundefs: HashMap<String, FunDef>,
                        filename: &Option<String>,
                        extra_fundefs: Option<&Vec<FunDef>>,
                        num_tests: i32) -> String {
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

    let (test_fun_name, test_fun) = match fundefs.get(TEST_GEN_FUN_NAME) {
      Option::None => ("_main", main_fun),
      Option::Some(f) => (TEST_GEN_FUN_NAME, f),
    };

    let mut rng = rand::thread_rng();
    let test_arg_vecs = (&test_fun.params).into_iter()
        .map(|param| (0..num_tests).into_iter()
             .map(|_| match param.get_type() {
               None => panic!("Parameter without type in main function."),
               Some(ty) => match ty {
                 Type::Bool => Expression::ConstInt(rng.gen_range(0..1)),
                 Type::Int => Expression::ConstInt(rng.gen()),
                 Type::Float => Expression::ConstFloat(rng.gen()),
                 _ => panic!("Unsupported: randomly generated {:?}", ty),
               }
             }).collect::<Vec<_>>())
        .collect::<Vec<_>>();
    let test_arg_decls = test_arg_vecs.into_iter().enumerate()
        .map(|(i, arg_vec)| BlockItem::Declaration(Declaration {
          specifiers: vec!(DeclarationSpecifier::TypeSpecifier(Type::Int)),
          declarator: Declarator::Array {
            name: format!("_inputs_{}", i),
            sizes: Vec::new()
          },
          initializer: Some(Initializer::List(arg_vec.into_iter()
            .map(|expr| Initializer::Expression(expr))
            .collect())),
        })).collect::<Vec<_>>();

    let timeout_handler = CRel::FunctionDefinition {
      specifiers: vec!(DeclarationSpecifier::TypeSpecifier(Type::Void)),
      name: "timeout_handler".to_string(),
      params: vec!(ParameterDeclaration {
        specifiers: vec!(DeclarationSpecifier::TypeSpecifier(Type::Int)),
        declarator: Some(Declarator::Identifier{ name: "signum".to_string() }),
      }),
      body: Box::new(Statement::Expression(Box::new(Expression::Call {
        callee: Box::new(Expression::Identifier{ name: "exit".to_string() }),
        args: vec!(Expression::Identifier{ name: "signum".to_string() }),
      }))),
    };

    let test_runner = CRel::FunctionDefinition {
      specifiers: vec!(DeclarationSpecifier::TypeSpecifier(Type::Void)),
      name: "_run_test".to_string(),
      params: (&test_fun.params).into_iter().enumerate()
        .map(|(i, param)| ParameterDeclaration {
          specifiers: param.specifiers.clone(),
          declarator: Some(Declarator::Identifier{ name: format!("_input_{}", i) }),
        }).collect(),
      body: Box::new(Statement::Compound(vec!(
        BlockItem::Declaration(Declaration {
          // Type should technically be pid_t
          specifiers: vec!(DeclarationSpecifier::TypeSpecifier(Type::Int)),
          declarator: Declarator::Identifier{ name: "pid".to_string() },
          initializer: None,
        }),
        BlockItem::Statement(Statement::Expression(Box::new(
          Expression::Binop {
            lhs: Box::new(Expression::Identifier{ name: "pid".to_string() }),
            rhs: Box::new(Expression::Call {
              callee: Box::new(Expression::Identifier{name: "fork".to_string()}),
              args: Vec::new(),
            }),
            op: BinaryOp::Assign,
          }))),
        BlockItem::Statement(Statement::If {
          condition: Box::new(Expression::Binop {
            lhs: Box::new(Expression::Identifier{ name: "pid".to_string() }),
            rhs: Box::new(Expression::ConstInt(0)),
            op: BinaryOp::Lt,
          }),
          then: Box::new(Statement::Compound(vec!(
            BlockItem::Statement(Statement::Expression(Box::new(Expression::Call {
              callee: Box::new(Expression::Identifier{ name: "printf".to_string() }),
              args: vec!(Expression::StringLiteral("Failed to fork.\\n".to_string())),
            }))),
            BlockItem::Statement(Statement::Expression(Box::new(Expression::Call {
              callee: Box::new(Expression::Identifier{ name: "exit".to_string() }),
              args: vec!(Expression::ConstInt(-1)),
            }))),
          ))),
          els: None,
        }),
        BlockItem::Statement(Statement::If {
          condition: Box::new(Expression::Binop {
            lhs: Box::new(Expression::Identifier{ name: "pid".to_string() }),
            rhs: Box::new(Expression::ConstInt(0)),
            op: BinaryOp::Equals,
          }),
          then: Box::new(Statement::Compound(vec!(
            BlockItem::Statement(Statement::Expression(Box::new(Expression::Call {
              callee: Box::new(Expression::Identifier{ name: "signal".to_string() }),
              args: vec!(
                Expression::Identifier{ name: "SIGALRM".to_string() },
                Expression::Identifier{ name: "timeout_handler".to_string() },
              ),
            }))),
            BlockItem::Statement(Statement::Expression(Box::new(Expression::Call {
              callee: Box::new(Expression::Identifier{ name: "alarm".to_string() }),
              args: vec!(Expression::ConstInt(2)),
            }))),
            BlockItem::Statement(Statement::Expression(Box::new(Expression::Call {
              callee: Box::new(Expression::Identifier{ name: test_fun_name.to_string() }),
              args: (0..test_fun.params.len()).into_iter().map(|i| Expression::Identifier {
                name: format!("_input_{}", i)
              }).collect(),
            }))),
            BlockItem::Statement(Statement::Expression(Box::new(Expression::Call {
              callee: Box::new(Expression::Identifier{ name: "exit".to_string() }),
              args: vec!(Expression::ConstInt(0)),
            }))),
          ))),
          els: Some(Box::new(Statement::Compound(vec!(
            BlockItem::Declaration(Declaration {
              specifiers: vec!(DeclarationSpecifier::TypeSpecifier(Type::Int)),
              declarator: Declarator::Identifier{ name: "status".to_string() },
              initializer: None,
            }),
            BlockItem::Statement(Statement::Expression(Box::new(Expression::Call {
              callee: Box::new(Expression::Identifier{ name: "waitpid".to_string() }),
              args: vec!(
                Expression::Identifier{ name: "pid".to_string() },
                Expression::Identifier{ name: "&status".to_string() },
                Expression::ConstInt(0),
              ),
            }))),
            BlockItem::Statement(Statement::If {
              condition: Box::new(Expression::Binop {
                lhs: Box::new(Expression::Identifier{ name: "status".to_string() }),
                rhs: Box::new(Expression::ConstInt(0)),
                op: BinaryOp::NotEquals,
              }),
              then: Box::new(Statement::Expression(Box::new(Expression::Call {
                callee: Box::new(Expression::Identifier{ name: "printf".to_string() }),
                args: vec!(Expression::StringLiteral("Test Case Failed\\n".to_string())),
              }))),
              els: None,
            }),
          )))),
        }),
      ))),
    };

    let driver = CRel::FunctionDefinition {
      specifiers: vec!(DeclarationSpecifier::TypeSpecifier(Type::Int)),
      name: "main".to_string(),
      params: Vec::new(),
      body: Box::new(Statement::Compound(vec![
        BlockItem::Statement(Statement::Compound(test_arg_decls)),
        BlockItem::Declaration(Declaration {
          specifiers: vec!(DeclarationSpecifier::TypeSpecifier(Type::Int)),
          declarator: Declarator::Identifier{name: "test_id".to_string()},
          initializer: Some(Initializer::Expression(Expression::ConstInt(0))),
        }),
        BlockItem::Statement(Statement::While {
          id: Uuid::new_v4(),
          runoff_link_id: None,
          invariants: Vec::new(),
          condition: Box::new(Expression::Binop {
            lhs: Box::new(Expression::Identifier{name: "test_id".to_string()}),
            rhs: Box::new(Expression::ConstInt(num_tests)),
            op: BinaryOp::Lt,
          }),
          body: Some(Box::new(Statement::Compound(vec!(
            BlockItem::Statement(Statement::Expression(Box::new(Expression::Call {
              callee: Box::new(Expression::Identifier{name: "_run_test".to_string()}),
              args: (0..test_fun.params.len()).into_iter()
                .map(|i| Expression::Binop {
                  lhs: Box::new(Expression::Identifier {
                    name: format!("_inputs_{}", i)
                  }),
                  rhs: Box::new(Expression::Identifier{name: "test_id".to_string()}),
                  op: BinaryOp::Index,
                }).collect(),
            }))),
            BlockItem::Statement(Statement::Expression(Box::new(Expression::Binop {
              lhs: Box::new(Expression::Identifier{name: "test_id".to_string()}),
              rhs: Box::new(Expression::Binop {
                lhs: Box::new(Expression::Identifier{name: "test_id".to_string()}),
                rhs: Box::new(Expression::ConstInt(1)),
                op: BinaryOp::Add,
              }),
              op: BinaryOp::Assign,
            }))),
          )))),
          is_runoff: false,
          is_merged: false,
        }),
        BlockItem::Statement(Statement::Return(
          Some(Box::new(Expression::ConstInt(0)))))
      ])),
    };

    let mut new_seq: Vec<CRel> = global_decls.iter()
      .map(|decl| match &decl.declarator {
        Declarator::Function{name, params} => {
          match fundefs.get(&format!("_{}", name)) {
            None => fun_impl_hash(&decl.specifiers, name.clone(), params),
            Some(def) => CRel::FunctionDefinition {
              specifiers: decl.specifiers.clone(),
              name: name.clone(),
              params: def.params.clone(),
              body: Box::new(def.body.clone()),
            },
          }
        },
        _ => CRel::Declaration(decl.clone()),
      })
      .collect();

    for fundef in extra_fundefs.unwrap_or(&vec!()) {
      new_seq.push(CRel::FunctionDefinition {
        specifiers: fundef.specifiers.clone(),
        name: fundef.name.clone(),
        params: fundef.params.clone(),
        body: Box::new(fundef.body.clone()),
      });
    }

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
    new_seq.push(timeout_handler);
    new_seq.push(test_runner);
    new_seq.push(driver);
    format!("{}\n{}", self.top(filename), CRel::Seq(new_seq).to_c(false, false))
  }

  pub fn crel_to_c(&self,
                   crel: &CRel,
                   precond: &KestrelCond,
                   postcond: &KestrelCond,
                   global_decls: Vec<Declaration>,
                   filename: &Option<String>) -> String {
    let (_, fundefs) = crate::crel::fundef::extract_fundefs(crel);
    let main_fun = fundefs.get("main").expect("No main function found");

    let param_inits = self.build_param_inits(&main_fun.params);
    let preconds  = BlockItem::Statement(precond.to_crel(StatementKind::Assume));
    let postconds = BlockItem::Statement(postcond.to_crel(StatementKind::Assert));

    let mut body_items: Vec<BlockItem> = Vec::new();
    if let Some(mut param_inits) = param_inits.clone() { body_items.append(&mut param_inits) }
    body_items.push(preconds);
    body_items.push(BlockItem::Statement(main_fun.body.clone()));
    body_items.push(postconds);
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
    format!("{}\n{}", self.top(filename), CRel::Seq(new_seq).to_c(false, false))
  }

  fn top(&self, filename: &Option<String>) -> String {
    match self {
      OutputMode::Daikon => {
        [
          "#include <signal.h>",
          "#include <stdio.h>",
          "#include <stdlib.h>",
          "#include <string.h>",
          "#include <sys/wait.h>",
          "#include <unistd.h>",
          "#include \"assert.h\"",
        ].join("\n")
      },
      OutputMode::Dafny => {
        "".to_string()
      },
      OutputMode::Icra => {
        "#include \"assert.h\"".to_string()
      },
      OutputMode::Seahorn => {
        [
          "#include \"seahorn/seahorn.h\"",
          "extern int arb_int();",
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
          "int arb_int();",
        ].join("\n")
      },
    }
  }

  pub fn crel_config(&self) -> to_crel::Config {
    to_crel::Config {
      assert_name: Some("assert".to_string()),
      assume_name: Some("assume".to_string()),
      nondet_name: self.nondet_name(),
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
          Some(Initializer::Expression(call_nondet_int.clone()))
        } else {
          None
        };
        BlockItem::Declaration(
          Declaration {
            specifiers: param.specifiers.clone(),
            declarator: param.declarator.as_ref().unwrap().clone(),
            initializer,
          }
        )
      })
      .collect())
  }
}
