//! Representation of unaligned programs given as input to KestRel.

use crate::crel::ast::*;
use crate::crel::blockify::*;
use crate::crel::fundef::FunDef;
use crate::elaenia::elaenia_spec::ElaeniaSpec;
use crate::names::*;
use crate::spec::KestrelSpec;
use std::collections::{HashMap, HashSet};

#[derive(Clone)]
pub struct UnalignedCRel {
  pub global_decls: Vec<Declaration>,
  pub fundefs: HashMap<String, FunDef>,
  pub params: Vec<ParameterDeclaration>,
  pub main: CRel,
}

impl UnalignedCRel {

  pub fn from_kestrel_spec(crel: &CRel, spec: &KestrelSpec) -> Self {
    UnalignedCRel::from(&crel, &spec.left, &spec.right)
  }

  pub fn from_elaenia_spec(crel: &CRel, spec: &ElaeniaSpec) -> Self {
    UnalignedCRel::from(&crel, &spec.afun, &spec.efun)
  }

  pub fn from(crel: &CRel, left_fun_name: &String, right_fun_name: &String) -> Self {

    let (global_decls, fundefs) = crate::crel::fundef::extract_fundefs(crel);

    let mut globals = global_vars(&global_decls);
    for f_seahorn in ["assume", "assert", "sassert"] {
      globals.insert(f_seahorn.to_string());
    }

    let left_fun = fundefs.get(left_fun_name)
      .unwrap_or_else(|| panic!("Function not found: {}", left_fun_name));
    let right_fun = fundefs.get(right_fun_name)
      .unwrap_or_else(|| panic!("Function not found: {}", right_fun_name));

    let left_fun = left_fun.map_vars(&|s: String| {
      if globals.contains(&s) { s } else { format!("l_{}", s) }
    });
    let right_fun = right_fun.map_vars(&|s: String| {
      if globals.contains(&s) { s } else { format!("r_{}", s) }
    });

    let mut params = left_fun.params.clone();
    params.append(&mut right_fun.params.clone());

    let main = CRel::FunctionDefinition {
      specifiers: vec!(DeclarationSpecifier::TypeSpecifier(Type::Void)),
      name: "main".to_string(),
      params: params.clone(),
      body: Box::new(Statement::Relation {
        lhs: Box::new(left_fun.body.blockify()),
        rhs: Box::new(right_fun.body.blockify()),
      })
    };

    UnalignedCRel {
      global_decls,
      fundefs: fundefs.clone(),
      params,
      main,
    }
  }

  pub fn global_decls_and_params(&self) -> Vec<Declaration> {
    let param_decls = self.params.iter()
      .filter_map(|p| p.as_declaration());
    let mut all_decls = self.global_decls.clone();
    all_decls.extend(param_decls);
    all_decls
  }
}

fn global_vars(decls: &Vec<Declaration>) -> HashSet<String> {
  let mut vars = HashSet::new();
  for decl in decls {
    vars.insert(declarator_name(&decl.declarator));
  }
  vars
}

fn declarator_name(decl: &Declarator) -> String {
  match &decl {
    Declarator::Identifier{name} => name.clone(),
    Declarator::Array{name, sizes:_} => name.clone(),
    Declarator::Function{name, params:_} => name.clone(),
    Declarator::Pointer(decl) => declarator_name(decl),
  }
}
