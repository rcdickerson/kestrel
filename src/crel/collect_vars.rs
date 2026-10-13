use crate::names::{CollectVars, all_vars, union_all, singleton};
use crate::names::{CollectVarTypes, all_var_types, union_all_types};
use crate::names::{CollectVarAccessTypes, all_var_access_types, union_all_access_types};
use crate::crel::ast::*;
use std::collections::HashMap;
use std::collections::HashSet;

impl CollectVars for CRel {
  fn vars(&self) -> HashSet<String> {
    match self {
      CRel::Declaration(decl) => decl.vars(),
      CRel::FunctionDefinition{specifiers:_, name, params, body} => {
        union_all(vec!(
          singleton(name.clone()),
          all_vars(params.clone()),
          body.vars(),
        ))
      },
      CRel::Seq(crels) => all_vars(crels.clone()),
    }
  }
}

impl CollectVars for Expression {
  fn vars(&self) -> HashSet<String> {
    match self {
      Expression::Identifier{name} => singleton(name.clone()),
      Expression::ConstBool(_) => HashSet::new(),
      Expression::ConstInt(_) => HashSet::new(),
      Expression::ConstFloat(_) => HashSet::new(),
      Expression::StringLiteral(_) => HashSet::new(),
      Expression::Call{callee, args} => {
        union_all(vec!(
          callee.vars(),
          all_vars(args.clone()),
        ))
      },
      Expression::ChoiceCall{callee, args} => {
        union_all(vec!(
          callee.vars(),
          all_vars(args.clone()),
        ))
      },
      Expression::Ternary { condition, then, els } => {
        union_all(vec!(
          condition.vars(),
          then.vars(),
          els.vars(),
        ))
      },
      Expression::Unop{expr, op: _} => expr.vars(),
      Expression::Binop{lhs, rhs, op: _} => {
        union_all(vec!(lhs.vars(), rhs.vars()))
      },
      Expression::Cast{expr, ..} => expr.vars(),
      Expression::Forall{condition, ..} => condition.vars(),
      Expression::SketchHole => HashSet::new(),
      Expression::Statement(stmt) => stmt.vars(),
    }
  }
}

impl CollectVars for Statement {
  fn vars(&self) -> HashSet<String> {
    match self {
      Statement::Assert(expr) => expr.vars(),
      Statement::Assume(expr) => expr.vars(),
      Statement::BasicBlock(items) => all_vars(items.clone()),
      Statement::Break => HashSet::new(),
      Statement::Compound(items) => all_vars(items.clone()),
      Statement::Expression(expr) => expr.vars(),
      Statement::GuardedRepeat{condition, body, ..} => {
        union_all(vec!(condition.vars(), body.vars()))
      }
      Statement::If{condition, then, els} => {
        union_all(vec!(
          condition.vars(),
          then.vars(),
          match els {
            None => HashSet::new(),
            Some(stmt) => stmt.vars(),
          },
        ))
      },
      Statement::None => HashSet::new(),
      Statement::Relation{lhs, rhs} => {
        union_all(vec!(lhs.vars(), rhs.vars()))
      },
      Statement::Return(expr) => {
        match expr {
          None => HashSet::new(),
          Some(expr) => expr.vars(),
        }
      },
      Statement::While{condition, body, ..} => {
        match body {
          None => condition.vars(),
          Some(body) => union_all(vec!(condition.vars(), body.vars()))
        }
      },
      Statement::WhileRel{condition_left, condition_right, body_left, body_right, body_merged, ..} => {
        let mut vars = vec! [condition_left.vars(), condition_right.vars()];
        body_left.as_ref().map(|body| vars.push(body.vars()));
        body_right.as_ref().map(|body| vars.push(body.vars()));
        body_merged.as_ref().map(|body| vars.push(body.vars()));
        union_all(vars)
      },
    }
  }
}

impl CollectVars for Declaration {
  fn vars(&self) -> HashSet<String> {
    match &self.initializer {
      None => self.declarator.vars(),
      Some(expr) => union_all(vec!(
        self.declarator.vars(),
        expr.vars()))
    }
  }
}

impl CollectVars for Declarator {
  fn vars(&self) -> HashSet<String> {
    match self {
      Declarator::Identifier{name} => singleton(name.clone()),
      Declarator::Array{name, sizes} => {
        let mut vars = sizes.iter()
          .map(|expr| expr.vars())
          .collect::<Vec<HashSet<String>>>();
        vars.push(singleton(name.clone()));
        union_all(vars)
      },
      Declarator::Function{name, params} => {
        let mut vars : Vec<HashSet<String>> = params.iter()
          .map(|p| p.vars())
          .collect();
        vars.push(singleton(name.clone()));
        union_all(vars)
      },
      Declarator::Pointer(decl) => {
        decl.vars()
      }
    }
  }
}

impl CollectVars for Initializer {
  fn vars(&self) -> HashSet<String> {
    match self {
      Initializer::Expression(expr) => expr.vars(),
      Initializer::List(exprs) => union_all(exprs.into_iter()
          .map(|expr| expr.vars())
          .collect::<Vec<_>>()),
    }
  }
}

impl CollectVars for ParameterDeclaration {
  fn vars(&self) -> HashSet<String> {
    match &self.declarator {
      None => HashSet::new(),
      Some(decl) => decl.vars(),
    }
  }
}

 impl CollectVars for BlockItem {
  fn vars(&self) -> HashSet<String> {
    match self {
      BlockItem::Declaration(decl) => decl.vars(),
      BlockItem::Statement(stmt) => stmt.vars(),
    }
  }
}

impl CollectVarTypes for CRel {
  fn var_types(&self) -> HashMap<String, TypeName> {
    match self {
      CRel::Declaration(decl) => decl.var_types(),
      CRel::FunctionDefinition{specifiers:_, name:_, params, body} => {
        union_all_types(vec!(
          all_var_types(params.clone()),
          body.var_types(),
        ))
      },
      CRel::Seq(crels) => all_var_types(crels.clone()),
    }
  }
}

impl CollectVarTypes for Expression {
  fn var_types(&self) -> HashMap<String, TypeName> {
    match self {
      Expression::Identifier{..} => HashMap::new(),
      Expression::ConstBool(_) => HashMap::new(),
      Expression::ConstInt(_) => HashMap::new(),
      Expression::ConstFloat(_) => HashMap::new(),
      Expression::StringLiteral(_) => HashMap::new(),
      Expression::Call{callee, args} => {
        union_all_types(vec!(
          callee.var_types(),
          all_var_types(args.clone()),
        ))
      },
      Expression::ChoiceCall{callee, args} => {
        union_all_types(vec!(
          callee.var_types(),
          all_var_types(args.clone()),
        ))
      },
      Expression::Ternary { condition, then, els } => {
        union_all_types(vec!(
          condition.var_types(),
          then.var_types(),
          els.var_types(),
        ))
      },
      Expression::Unop{expr, op: _} => expr.var_types(),
      Expression::Binop{lhs, rhs, op: _} => {
        union_all_types(vec!(lhs.var_types(), rhs.var_types()))
      },
      Expression::Cast{expr, ..} => expr.var_types(),
      Expression::Forall{condition, ..} => condition.var_types(),
      Expression::SketchHole => HashMap::new(),
      Expression::Statement(stmt) => stmt.var_types(),
    }
  }
}

impl CollectVarTypes for Statement {
  fn var_types(&self) -> HashMap<String, TypeName> {
    match self {
      Statement::Assert(expr) => expr.var_types(),
      Statement::Assume(expr) => expr.var_types(),
      Statement::BasicBlock(items) => all_var_types(items.clone()),
      Statement::Break => HashMap::new(),
      Statement::Compound(items) => all_var_types(items.clone()),
      Statement::Expression(expr) => expr.var_types(),
      Statement::GuardedRepeat{condition, body, ..} => {
        union_all_types(vec!(condition.var_types(), body.var_types()))
      }
      Statement::If{condition, then, els} => {
        union_all_types(vec!(
          condition.var_types(),
          then.var_types(),
          match els {
            None => HashMap::new(),
            Some(stmt) => stmt.var_types(),
          },
        ))
      },
      Statement::None => HashMap::new(),
      Statement::Relation{lhs, rhs} => {
        union_all_types(vec!(lhs.var_types(), rhs.var_types()))
      },
      Statement::Return(expr) => {
        match expr {
          None => HashMap::new(),
          Some(expr) => expr.var_types(),
        }
      },
      Statement::While{condition, body, ..} => {
        match body {
          None => condition.var_types(),
          Some(body) => union_all_types(vec!(condition.var_types(), body.var_types()))
        }
      },
      Statement::WhileRel{condition_left, condition_right, body_left, body_right, body_merged, ..} => {
        let mut types = vec! [condition_left.var_types(), condition_right.var_types()];
        body_left.as_ref().map(|body| types.push(body.var_types()));
        body_right.as_ref().map(|body| types.push(body.var_types()));
        body_merged.as_ref().map(|body| types.push(body.var_types()));
        union_all_types(types)
      },
    }
  }
}

impl CollectVarTypes for Declaration {
  fn var_types(&self) -> HashMap<String, TypeName> {
    let mut types = match &self.initializer {
      None => self.declarator.var_types(),
      Some(expr) => union_all_types(vec!(
        self.declarator.var_types(),
        expr.var_types()))
    };
    types.insert(self.declarator.name(), declared_type(&self.specifiers, &self.declarator));
    types
  }
}

impl CollectVarTypes for Declarator {
  fn var_types(&self) -> HashMap<String, TypeName> {
    match self {
      Declarator::Identifier{..} => HashMap::new(),
      Declarator::Array{sizes, ..} => {
        let types = sizes.iter()
          .map(|expr| expr.var_types())
          .collect::<Vec<HashMap<String, TypeName>>>();
        union_all_types(types)
      },
      Declarator::Function{params, ..} => {
        let types : Vec<HashMap<String, TypeName>> = params.iter()
          .map(|p| p.var_types())
          .collect();
        union_all_types(types)
      },
      Declarator::Pointer(decl) => {
        decl.var_types()
      }
    }
  }
}

impl CollectVarTypes for Initializer {
  fn var_types(&self) -> HashMap<String, TypeName> {
    match self {
      Initializer::Expression(expr) => expr.var_types(),
      Initializer::List(exprs) => union_all_types(exprs.into_iter()
          .map(|expr| expr.var_types())
          .collect::<Vec<_>>()),
    }
  }
}

impl CollectVarTypes for ParameterDeclaration {
  fn var_types(&self) -> HashMap<String, TypeName> {
    match &self.declarator {
      None => HashMap::new(),
      Some(decl) => {
        let mut types = decl.var_types();
        types.insert(decl.name(), declared_type(&self.specifiers, decl));
        types
      },
    }
  }
}

impl CollectVarTypes for BlockItem {
  fn var_types(&self) -> HashMap<String, TypeName> {
    match self {
      BlockItem::Declaration(decl) => decl.var_types(),
      BlockItem::Statement(stmt) => stmt.var_types(),
    }
  }
}

fn declared_type(specifiers: &Vec<DeclarationSpecifier>, declarator: &Declarator) -> TypeName {
  let base = TypeName::Base(specifiers.iter().filter_map(|spec| match spec {
    DeclarationSpecifier::TypeSpecifier(ty) => Some(ty.clone()),
    _ => None,
  }).collect());
  declarator_type(base, declarator)
}

fn declarator_type(ty: TypeName, declarator: &Declarator) -> TypeName {
  match declarator {
    Declarator::Pointer(inner) => declarator_type(TypeName::Pointer(Box::new(ty)), inner),
    Declarator::Array{sizes, ..} => sizes.iter().rev().fold(ty, |ty, size| match const_size(size) {
      Some(n) => TypeName::Array(Box::new(ty), n as usize),
      None => ty,
    }),
    _ => ty,
  }
}

fn const_size(size: &Expression) -> Option<i32> {
  match size {
    Expression::ConstInt(n) => Some(*n),
    Expression::Binop{lhs, rhs, op} => {
      let (l, r) = (const_size(lhs)?, const_size(rhs)?);
      match op {
        BinaryOp::Add => Some(l + r),
        BinaryOp::Sub => Some(l - r),
        BinaryOp::Mul => Some(l * r),
        _ => None,
      }
    },
    _ => None,
  }
}

impl CollectVarAccessTypes for CRel {
  fn var_access_types(&self) -> HashMap<String, Vec<TypeName>> {
    match self {
      CRel::Declaration(decl) => decl.var_access_types(),
      CRel::FunctionDefinition{specifiers:_, name:_, params, body} => {
        union_all_access_types(vec!(
          all_var_access_types(params.clone()),
          body.var_access_types(),
        ))
      },
      CRel::Seq(crels) => all_var_access_types(crels.clone()),
    }
  }
}

impl CollectVarAccessTypes for Expression {
  fn var_access_types(&self) -> HashMap<String, Vec<TypeName>> {
    match self {
      Expression::Identifier{..} => HashMap::new(),
      Expression::ConstBool(_) => HashMap::new(),
      Expression::ConstInt(_) => HashMap::new(),
      Expression::ConstFloat(_) => HashMap::new(),
      Expression::StringLiteral(_) => HashMap::new(),
      Expression::Call{callee, args} => {
        union_all_access_types(vec!(
          callee.var_access_types(),
          all_var_access_types(args.clone()),
        ))
      },
      Expression::ChoiceCall{callee, args} => {
        union_all_access_types(vec!(
          callee.var_access_types(),
          all_var_access_types(args.clone()),
        ))
      },
      Expression::Ternary { condition, then, els } => {
        union_all_access_types(vec!(
          condition.var_access_types(),
          then.var_access_types(),
          els.var_access_types(),
        ))
      },
      Expression::Unop{expr, op: _} => match punned_access(self) {
        Some((name, ty)) => HashMap::from([(name, vec!(ty))]),
        None => expr.var_access_types(),
      },
      Expression::Binop{lhs, rhs, op: _} => {
        union_all_access_types(vec!(lhs.var_access_types(), rhs.var_access_types()))
      },
      Expression::Cast{expr, ..} => expr.var_access_types(),
      Expression::Forall{condition, ..} => condition.var_access_types(),
      Expression::SketchHole => HashMap::new(),
      Expression::Statement(stmt) => stmt.var_access_types(),
    }
  }
}

impl CollectVarAccessTypes for Statement {
  fn var_access_types(&self) -> HashMap<String, Vec<TypeName>> {
    match self {
      Statement::Assert(expr) => expr.var_access_types(),
      Statement::Assume(expr) => expr.var_access_types(),
      Statement::BasicBlock(items) => all_var_access_types(items.clone()),
      Statement::Break => HashMap::new(),
      Statement::Compound(items) => all_var_access_types(items.clone()),
      Statement::Expression(expr) => expr.var_access_types(),
      Statement::GuardedRepeat{condition, body, ..} => {
        union_all_access_types(vec!(condition.var_access_types(), body.var_access_types()))
      }
      Statement::If{condition, then, els} => {
        union_all_access_types(vec!(
          condition.var_access_types(),
          then.var_access_types(),
          match els {
            None => HashMap::new(),
            Some(stmt) => stmt.var_access_types(),
          },
        ))
      },
      Statement::None => HashMap::new(),
      Statement::Relation{lhs, rhs} => {
        union_all_access_types(vec!(lhs.var_access_types(), rhs.var_access_types()))
      },
      Statement::Return(expr) => {
        match expr {
          None => HashMap::new(),
          Some(expr) => expr.var_access_types(),
        }
      },
      Statement::While{condition, body, ..} => {
        match body {
          None => condition.var_access_types(),
          Some(body) => union_all_access_types(vec!(condition.var_access_types(), body.var_access_types()))
        }
      },
      Statement::WhileRel{condition_left, condition_right, body_left, body_right, body_merged, ..} => {
        let mut types = vec! [condition_left.var_access_types(), condition_right.var_access_types()];
        body_left.as_ref().map(|body| types.push(body.var_access_types()));
        body_right.as_ref().map(|body| types.push(body.var_access_types()));
        body_merged.as_ref().map(|body| types.push(body.var_access_types()));
        union_all_access_types(types)
      },
    }
  }
}

impl CollectVarAccessTypes for Declaration {
  fn var_access_types(&self) -> HashMap<String, Vec<TypeName>> {
    match &self.initializer {
      None => self.declarator.var_access_types(),
      Some(expr) => union_all_access_types(vec!(
        self.declarator.var_access_types(),
        expr.var_access_types()))
    }
  }
}

impl CollectVarAccessTypes for Declarator {
  fn var_access_types(&self) -> HashMap<String, Vec<TypeName>> {
    match self {
      Declarator::Identifier{..} => HashMap::new(),
      Declarator::Array{sizes, ..} => {
        let types = sizes.iter()
          .map(|expr| expr.var_access_types())
          .collect::<Vec<HashMap<String, Vec<TypeName>>>>();
        union_all_access_types(types)
      },
      Declarator::Function{params, ..} => {
        let types : Vec<HashMap<String, Vec<TypeName>>> = params.iter()
          .map(|p| p.var_access_types())
          .collect();
        union_all_access_types(types)
      },
      Declarator::Pointer(decl) => {
        decl.var_access_types()
      }
    }
  }
}

impl CollectVarAccessTypes for Initializer {
  fn var_access_types(&self) -> HashMap<String, Vec<TypeName>> {
    match self {
      Initializer::Expression(expr) => expr.var_access_types(),
      Initializer::List(exprs) => union_all_access_types(exprs.into_iter()
          .map(|expr| expr.var_access_types())
          .collect::<Vec<_>>()),
    }
  }
}

impl CollectVarAccessTypes for ParameterDeclaration {
  fn var_access_types(&self) -> HashMap<String, Vec<TypeName>> {
    match &self.declarator {
      None => HashMap::new(),
      Some(decl) => decl.var_access_types(),
    }
  }
}

impl CollectVarAccessTypes for BlockItem {
  fn var_access_types(&self) -> HashMap<String, Vec<TypeName>> {
    match self {
      BlockItem::Declaration(decl) => decl.var_access_types(),
      BlockItem::Statement(stmt) => stmt.var_access_types(),
    }
  }
}

fn punned_access(expr: &Expression) -> Option<(String, TypeName)> {
  if let Expression::Unop{expr: cast, op: UnaryOp::Deref} = expr {
    if let Expression::Cast{ty: TypeName::Pointer(ty), expr: addr} = cast.as_ref() {
      if let Expression::Unop{expr: var, op: UnaryOp::Address} = addr.as_ref() {
        if let Expression::Identifier{name} = var.as_ref() {
          return Some((name.clone(), (**ty).clone()));
        }
      }
    }
  }
  None
}

#[cfg(test)]
mod test {
  use super::*;

  #[test]
  fn test_collect_vars() {
    let prog = CRel::FunctionDefinition {
      specifiers: vec!(),
      name: "foo".to_string(),
      params: vec!(ParameterDeclaration {
        specifiers: vec!(DeclarationSpecifier::TypeSpecifier(Type::Int)),
        declarator: Some(Declarator::Identifier{name: "w".to_string()}),
      }),
      body: Box::new(Statement::If{
        condition: Box::new(Expression::Binop {
          lhs: Box::new(Expression::Identifier{name: "x".to_string()}),
          rhs: Box::new(Expression::Identifier{name: "y".to_string()}),
          op: BinaryOp::Equals
        }),
        then: Box::new(Statement::Expression(
          Box::new(Expression::Binop {
          lhs: Box::new(Expression::Identifier{name: "x".to_string()}),
          rhs: Box::new(Expression::Identifier{name: "y".to_string()}),
          op: BinaryOp::Add
        }))),
        els: Some(Box::new(Statement::Expression(
          Box::new(Expression::Identifier{name: "z".to_string()})))),
      })
    };

    let expected = ["foo", "w", "x", "y", "z"].iter()
      .map(|v| v.to_string())
      .collect::<HashSet<String>>();

    assert_eq!(prog.vars(), expected);
  }
}
