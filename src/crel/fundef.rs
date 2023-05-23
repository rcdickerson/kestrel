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

pub fn extract_fundefs(crel: &CRel) -> (Option<CRel>, HashMap<String, FunDef>) {
  match crel {
    CRel::Declaration{ specifiers: _, declarators: _ } => {
      (Some(crel.clone()), HashMap::new())
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
      (None, map)
    },
    CRel::Seq(crels) => {
      let (crels, defs): (Vec<_>, Vec<_>) = crels.iter()
        .map(|c| extract_fundefs(c))
        .unzip();
      let crels: Vec<_> = crels.iter().flatten().map(|c| (*c).clone()).collect();
      let mut def_union = HashMap::new();
      for def in defs {
        def_union.extend(def);
      }
      ( if crels.len() > 0 { Some(CRel::Seq(crels)) } else { None }, def_union )
    },
  }
}
