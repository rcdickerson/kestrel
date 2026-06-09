/// Represents a function definition a la CRel::FunctionDefinition.

use crate::crel::ast::*;
use crate::names::*;
use std::collections::HashMap;

#[derive(Clone, Debug)]
pub struct FunDef {
  pub specifiers: Vec<DeclarationSpecifier>,
  pub name: String,
  pub params: Vec<ParameterDeclaration>,
  pub body: Statement,
}

impl MapVars for FunDef {
  fn map_vars<F>(&self, f: &F) -> Self
    where F: Fn(String) -> String
  {
    FunDef {
      specifiers: self.specifiers.clone(),
      name: f(self.name.clone()),
      params: self.params.iter().map(|p| p.map_vars(f)).collect(),
      body: self.body.map_vars(f),
    }
  }
}

pub fn extract_fundefs(crel: &CRel) -> (Vec<Declaration>, HashMap<String, FunDef>) {
  match crel {
    CRel::Declaration(declaration) => {
      (vec!(declaration.clone()), HashMap::new())
    },
    CRel::FunctionDefinition{specifiers, name, params, body} => {
      (Vec::new(), HashMap::from([(name.clone(), FunDef {
        specifiers: specifiers.clone(),
        name: name.clone(),
        params: params.clone(),
        body: *body.clone(),
      })]))
    },
    CRel::Seq(crels) => {
      let (decls, defs): (Vec<_>, Vec<_>) = crels.iter()
        .map(extract_fundefs)
        .unzip();
      let decls: Vec<_> = decls.iter().flatten().map(|c| (*c).clone()).collect();
      let mut def_union = HashMap::new();
      for def in defs {
        def_union.extend(def);
      }
      (decls, def_union)
    },
  }
}
