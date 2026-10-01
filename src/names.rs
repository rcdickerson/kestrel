//! Utilities for working with names in program syntax.

use crate::crel::ast::TypeName;
use std::collections::HashMap;
use std::collections::HashSet;

pub trait CollectVars {
  fn vars(&self) -> HashSet<String>;
}

pub trait MapVars {
  fn map_vars<F>(&self, f: &F) -> Self where F: Fn(String) -> String;
}

pub fn all_vars<I>(collectable: I) -> HashSet<String>
  where
    I: IntoIterator,
    I::Item: CollectVars,
{
  union_all(collectable.into_iter().map(|c| c.vars()))
}

pub fn union_all<I>(sets: I) -> HashSet<String>
  where I: IntoIterator<Item = HashSet<String>>
{
  sets.into_iter().fold(HashSet::new(),
        |s, v| s.union(&v).cloned().collect())
}

pub fn singleton(s: String) -> HashSet<String> {
  let mut set = HashSet::new();
  set.insert(s);
  set
}

pub trait CollectVarTypes {
  fn var_types(&self) -> HashMap<String, TypeName>;
}

pub fn all_var_types<I>(collectable: I) -> HashMap<String, TypeName>
  where
    I: IntoIterator,
    I::Item: CollectVarTypes,
{
  union_all_types(collectable.into_iter().map(|c| c.var_types()))
}

pub fn union_all_types<I>(maps: I) -> HashMap<String, TypeName>
  where I: IntoIterator<Item = HashMap<String, TypeName>>
{
  maps.into_iter().fold(HashMap::new(),
        |mut m, v| { m.extend(v); m })
}
