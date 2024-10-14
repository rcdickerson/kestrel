use crate::crel::ast::*;

pub trait CRelMapper {
  fn map_crel(&mut self, crel: &CRel) -> CRel { crel.clone() }
  fn map_declarator(&mut self, decl: &Declarator) -> Declarator { decl.clone() }
  fn map_declaration(&mut self, decl: &Declaration) -> Declaration { decl.clone() }
  fn map_parameter_declaration(&mut self, pdecl: &ParameterDeclaration)
                               -> ParameterDeclaration { pdecl.clone() }
  fn map_declaration_specifier(&mut self, spec: &DeclarationSpecifier)
                               -> DeclarationSpecifier { spec.clone() }
  fn map_statement(&mut self, stmt: &Statement) -> Statement { stmt.clone() }
  fn map_expression(&mut self, expr: &Expression) -> Expression { expr.clone() }
  fn map_block_item(&mut self, item: &BlockItem) -> BlockItem { item.clone() }
  fn map_name(&mut self, name: &String) -> String { name.clone() }
}

impl CRel {
  pub fn map(&self, mapper: &mut dyn CRelMapper) -> CRel {
    match &self {
      CRel::Declaration(decl) => {
        CRel::Declaration(mapper.map_declaration(decl).map(mapper))
      },
      CRel::FunctionDefinition{specifiers, name, params, body} => CRel::FunctionDefinition {
        specifiers: specifiers.iter()
          .map(|spec| mapper.map_declaration_specifier(spec))
          .collect(),
        name: mapper.map_name(name),
        params: params.iter()
          .map(|param| mapper.map_parameter_declaration(param).map(mapper))
          .collect(),
        body: Box::new(mapper.map_statement(body).map(mapper)),
      },
      CRel::Seq(stmts) => CRel::Seq(stmts.iter().map(|stmt| {
        mapper.map_crel(stmt).map(mapper)
      }).collect())
    }
  }
}

impl Declarator {
  pub fn map(&self, mapper: &mut dyn CRelMapper) -> Declarator {
    match &self {
      Declarator::Identifier{name} => {
        Declarator::Identifier{name: mapper.map_name(name)}
      },
      Declarator::Array{name, sizes} => Declarator::Array {
        name: mapper.map_name(name),
        sizes: sizes.iter().map(|expr| mapper.map_expression(expr).map(mapper)).collect(),
      },
      Declarator::Function{name, params} => Declarator::Function {
        name: mapper.map_name(name),
        params: params.iter().map(|param| {
          mapper.map_parameter_declaration(param).map(mapper)
        }).collect(),
      },
      Declarator::Pointer(decl) => {
        Declarator::Pointer(Box::new(mapper.map_declarator(decl).map(mapper)))
      },
    }
  }
}

impl Declaration {
  pub fn map(&self, mapper: &mut dyn CRelMapper) -> Declaration {
    Declaration {
      specifiers: self.specifiers.iter().map(|spec| {
        mapper.map_declaration_specifier(spec)
      }).collect(),
      declarator: mapper.map_declarator(&self.declarator).map(mapper),
      initializer: self.initializer.as_ref().map(|init| {
        mapper.map_expression(&init).map(mapper)
      }),
    }
  }
}

impl ParameterDeclaration {
  pub fn map(&self, mapper: &mut dyn CRelMapper) -> ParameterDeclaration {
    ParameterDeclaration {
      specifiers: self.specifiers.iter().map(|spec| {
        mapper.map_declaration_specifier(spec)
      }).collect(),
      declarator: self.declarator.as_ref().map(|decl| {
        mapper.map_declarator(&decl).map(mapper)
      }),
    }
  }
}

impl Statement {
  pub fn map(&self, mapper: &mut dyn CRelMapper) -> Statement {
    match &self {
      Statement::BasicBlock(items) => Statement::BasicBlock (
        items.iter().map(|item| {
          mapper.map_block_item(item).map(mapper)
        }).collect()
      ),
      Statement::Break => Statement::Break,
      Statement::Compound(items) => Statement::Compound (
        items.iter().map(|item| {
          mapper.map_block_item(item).map(mapper)
        }).collect()
      ),
      Statement::Expression(expr) => Statement::Expression (
        Box::new(mapper.map_expression(expr).map(mapper))
      ),
      Statement::GuardedRepeat{id, repetitions, condition, body} => Statement::GuardedRepeat {
        id: id.clone(),
        repetitions: *repetitions,
        condition: Box::new(mapper.map_expression(condition)),
        body: Box::new(mapper.map_statement(body)),
      },
      Statement::If{condition, then, els} => Statement::If {
        condition: Box::new(mapper.map_expression(condition).map(mapper)),
        then: Box::new(mapper.map_statement(then).map(mapper)),
        els: els.as_ref().map(|stmt| {
          Box::new(mapper.map_statement(&stmt).map(mapper))
        }),
      },
      Statement::None => Statement::None,
      Statement::Relation{lhs, rhs} => Statement::Relation {
        lhs: Box::new(mapper.map_statement(lhs).map(mapper)),
        rhs: Box::new(mapper.map_statement(rhs).map(mapper)),
      },
      Statement::Return(expr) => Statement::Return (
        expr.as_ref().map(|expr| Box::new(mapper.map_expression(&expr).map(mapper)))
      ),
      Statement::While{id, runoff_link_id, invariants, condition, body, is_runoff, is_merged} => Statement::While {
        id: id.clone(),
        runoff_link_id: runoff_link_id.clone(),
        invariants: invariants.clone(),
        condition: Box::new(mapper.map_expression(condition).map(mapper)),
        body: body.as_ref().map(|stmt| {
          Box::new(mapper.map_statement(&stmt).map(mapper))
        }),
        is_runoff: *is_runoff,
        is_merged: *is_merged,
      },
    }
  }
}

impl Expression {
  pub fn map(&self, mapper: &mut dyn CRelMapper) -> Expression {
    match &self {
      Expression::Identifier{name} => Expression::Identifier {
        name: mapper.map_name(name)
      },
      Expression::ConstInt(_) => self.clone(),
      Expression::ConstFloat(_) => self.clone(),
      Expression::StringLiteral(_) => self.clone(),
      Expression::Call{callee, args} => Expression::Call {
        callee: Box::new(mapper.map_expression(callee).map(mapper)),
        args: args.iter().map(|arg| {
          mapper.map_expression(arg).map(mapper)
        }).collect(),
      },
      Expression::Unop{expr, op} => Expression::Unop {
        expr: Box::new(mapper.map_expression(expr).map(mapper)),
        op: op.clone(),
      },
      Expression::Binop{lhs, rhs, op} => Expression::Binop {
        lhs: Box::new(mapper.map_expression(lhs).map(mapper)),
        rhs: Box::new(mapper.map_expression(rhs).map(mapper)),
        op: op.clone(),
      },
      Expression::Forall{bindings, condition} => Expression::Forall {
        bindings: bindings.iter().map(|(v, t)| (mapper.map_name(v), t.clone())).collect(),
        condition: Box::new(mapper.map_expression(condition).map(mapper)),
      },
      Expression::Statement(stmt) => Expression::Statement(
        Box::new(mapper.map_statement(stmt).map(mapper))
      ),
    }
  }
}

impl BlockItem {
  pub fn map(&self, mapper: &mut dyn CRelMapper) -> BlockItem {
    match &self {
      BlockItem::Declaration(decl) => BlockItem::Declaration(
        mapper.map_declaration(decl).map(mapper)
      ),
      BlockItem::Statement(stmt) => BlockItem::Statement(
        mapper.map_statement(stmt).map(mapper)
      ),
    }
  }
}
