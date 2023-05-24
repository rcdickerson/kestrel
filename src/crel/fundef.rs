use crate::crel::ast::*;
use crate::names::*;
use std::collections::HashMap;

#[derive(Clone, Debug)]
pub struct FunDef {
  pub body: Statement,
  pub params: Vec<ParameterDeclaration>,
}
impl MapVars for FunDef {
  fn map_vars<F>(&self, f: &F) -> Self
    where F: Fn(String) -> String
  {
    FunDef {
      body: self.body.map_vars(f),
      params: self.params.iter().map(|p| p.map_vars(f)).collect(),
    }
  }
}

pub fn extract_fundefs(crel: &CRel) -> (Vec<Declaration>, HashMap<String, FunDef>) {
  match crel {
    CRel::Declaration(declaration) => {
      (vec!(declaration.clone()), HashMap::new())
    },
    CRel::FunctionDefinition{specifiers: _, name, params, body} => {
      let mut map = HashMap::new();
      map.insert(name.clone(), FunDef{body: *body.clone(), params: params.clone()});
      (Vec::new(), map)
    },
    CRel::Seq(crels) => {
      let (decls, defs): (Vec<_>, Vec<_>) = crels.iter()
        .map(|c| extract_fundefs(c))
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
