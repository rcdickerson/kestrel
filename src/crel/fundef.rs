use crate::crel::ast::*;
use crate::names::*;
use std::collections::HashMap;

#[derive(Clone, Debug)]
pub struct FunDef {
  // TODO: Params.
  pub body: Statement,
}
impl MapVars for FunDef {
  fn map_vars<F>(&self, f: &F) -> Self
    where F: Fn(String) -> String
  {
    FunDef{body: self.body.map_vars(f)}
  }
}

pub fn extract_fundefs(crel: &CRel) -> (Vec<InitDeclarator>, HashMap<String, FunDef>) {
  match crel {
    CRel::Declaration{specifiers: _, declarators} => {
      (declarators.clone(), HashMap::new())
    },
    CRel::FunctionDefinition{specifiers: _, name, params: _, body} => {
      let name = match name {
        Declarator::Identifier{name} => name.clone(),
        Declarator::Array{name:_, size:_} => {
          panic!("Cannot have array declarator as function name")
        },
        Declarator::Function{name, params:_} => name.clone(),
        Declarator::Pointer(_) => {
          panic!("Unsupported: pointer declarator as function name")
        }
      };
      let mut map = HashMap::new();
      map.insert(name, FunDef{
        body: *body.clone(),
      });
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
