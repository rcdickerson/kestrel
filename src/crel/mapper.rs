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
        let mapped_decl = decl.map(mapper);
        mapper.map_crel(&CRel::Declaration(mapped_decl))
      },
      CRel::FunctionDefinition{specifiers, name, params, body} => {
        let mapped_specifiers = specifiers.iter()
          .map(|spec| mapper.map_declaration_specifier(spec))
          .collect();
        let mapped_name = mapper.map_name(name);
        let mapped_params = params.iter()
          .map(|param| param.map(mapper))
          .collect();
        let mapped_body = body.map(mapper);
        mapper.map_crel(&CRel::FunctionDefinition {
          specifiers: mapped_specifiers,
          name: mapped_name,
          params: mapped_params,
          body: Box::new(mapped_body),
        })
      },
      CRel::Seq(stmts) => {
        let mapped_stmts = stmts.iter().map(|stmt| {
          mapper.map_crel(stmt).map(mapper)
        }).collect();
        mapper.map_crel(&CRel::Seq(mapped_stmts))
      },
    }
  }
}

impl Declarator {
  pub fn map(&self, mapper: &mut dyn CRelMapper) -> Declarator {
    match &self {
      Declarator::Identifier{name} => {
        let mapped_name = mapper.map_name(name);
        mapper.map_declarator(&Declarator::Identifier{name: mapped_name})
      },
      Declarator::Array{name, sizes} => {
        let mapped_name = mapper.map_name(name);
        let mapped_sizes = sizes.iter().map(|expr| expr.map(mapper)).collect();
        mapper.map_declarator(&Declarator::Array {
          name: mapped_name,
          sizes: mapped_sizes,
        })
      },
      Declarator::Function{name, params} => {
        let mapped_name = mapper.map_name(name);
        let mapped_params = params.iter().map(|param| {
          param.map(mapper)
        }).collect();
        mapper.map_declarator(&Declarator::Function {
          name: mapped_name,
          params: mapped_params,
        })
      },
      Declarator::Pointer(decl) => {
        let mapped_decl = decl.map(mapper);
        mapper.map_declarator(&Declarator::Pointer(Box::new(mapped_decl)))
      },
    }
  }
}

impl Declaration {
  pub fn map(&self, mapper: &mut dyn CRelMapper) -> Declaration {
    let mapped_specifiers = self.specifiers.iter().map(|spec| {
      mapper.map_declaration_specifier(spec)
    }).collect();
    let mapped_declarator = self.declarator.map(mapper);
    let mapped_initializer = self.initializer.as_ref().map(|init| {
      init.map(mapper)
    });
    mapper.map_declaration(&Declaration {
      specifiers: mapped_specifiers,
      declarator: mapped_declarator,
      initializer: mapped_initializer,
    })
  }
}

impl ParameterDeclaration {
  pub fn map(&self, mapper: &mut dyn CRelMapper) -> ParameterDeclaration {
    let mapped_specifiers = self.specifiers.iter().map(|spec| {
      mapper.map_declaration_specifier(spec)
    }).collect();
    let mapped_declarator = self.declarator.as_ref().map(|decl| {
      decl.map(mapper)
    });
    mapper.map_parameter_declaration(&ParameterDeclaration {
      specifiers: mapped_specifiers,
      declarator: mapped_declarator,
    })
  }
}

impl Statement {
  pub fn map(&self, mapper: &mut dyn CRelMapper) -> Statement {
    match &self {
      Statement::Assert(expr) => {
        let mapped_expr = expr.map(mapper);
        mapper.map_statement(&Statement::Assert(Box::new(mapped_expr)))
      },
      Statement::Assume(expr) => {
        let mapped_expr = expr.map(mapper);
        mapper.map_statement(&Statement::Assume(Box::new(mapped_expr)))
      },
      Statement::BasicBlock(items) => {
        let mapped_items = items.iter().map(|item| {
          item.map(mapper)
        }).collect();
        mapper.map_statement(&Statement::BasicBlock(mapped_items))
      },
      Statement::Break => mapper.map_statement(self),
      Statement::Compound(items) => {
        let mapped_items = items.iter().map(|item| {
          item.map(mapper)
        }).collect();
        mapper.map_statement(&Statement::Compound(mapped_items))
      },
      Statement::Expression(expr) => {
        let mapped_expr = expr.map(mapper);
        mapper.map_statement(&Statement::Expression(Box::new(mapped_expr)))
      },
      Statement::GuardedRepeat{id, repetitions, condition, body} => {
        let mapped_condition = condition.map(mapper);
        let mapped_body = body.map(mapper);
        mapper.map_statement(&Statement::GuardedRepeat {
          id: id.clone(),
          repetitions: *repetitions,
          condition: Box::new(mapped_condition),
          body: Box::new(mapped_body),
        })
      },
      Statement::If{condition, then, els} => {
        let mapped_condition = condition.map(mapper);
        let mapped_then = then.map(mapper);
        let mapped_els = els.as_ref().map(|stmt| { Box::new(stmt.map(mapper)) });
        mapper.map_statement(&Statement::If {
          condition: Box::new(mapped_condition),
          then: Box::new(mapped_then),
          els: mapped_els,
        })
      },
      Statement::None => mapper.map_statement(self),
      Statement::Relation{lhs, rhs} => {
        let mapped_lhs = lhs.map(mapper);
        let mapped_rhs = rhs.map(mapper);
        mapper.map_statement(&Statement::Relation {
          lhs: Box::new(mapped_lhs),
          rhs: Box::new(mapped_rhs),
        })
      },
      Statement::Return(expr) => {
        let mapped_expr = expr.as_ref().map(|expr| Box::new(expr.map(mapper)));
        mapper.map_statement(&Statement::Return(mapped_expr))
      },
      Statement::While{id, runoff_link_id, invariants, condition, body, is_runoff, is_merged} => {
        let mapped_condition = condition.map(mapper);
        let mapped_body = body.as_ref().map(|stmt| {
          Box::new(stmt.map(mapper))
        });
        mapper.map_statement(&Statement::While {
          id: id.clone(),
          runoff_link_id: runoff_link_id.clone(),
          invariants: invariants.clone(),
          condition: Box::new(mapped_condition),
          body: mapped_body,
          is_runoff: *is_runoff,
          is_merged: *is_merged,
        })
      },
    }
  }
}

impl Expression {
  pub fn map(&self, mapper: &mut dyn CRelMapper) -> Expression {
    match &self {
      Expression::Identifier{name} => {
        let mapped_name = mapper.map_name(name);
        mapper.map_expression(&Expression::Identifier {
          name: mapped_name,
        })
      },
      Expression::ConstInt(_) => mapper.map_expression(self),
      Expression::ConstFloat(_) => mapper.map_expression(self),
      Expression::StringLiteral(_) => mapper.map_expression(self),
      Expression::Call{callee, args} => {
        let mapped_callee = callee.map(mapper);
        let mapped_args = args.iter().map(|arg| {
          arg.map(mapper)
        }).collect();
        mapper.map_expression(&Expression::Call {
          callee: Box::new(mapped_callee),
          args: mapped_args,
        })
      },
      Expression::ASpecCall{callee, args} => {
        let mapped_callee = callee.map(mapper);
        let mapped_args = args.iter().map(|arg| {
          arg.map(mapper)
        }).collect();
        mapper.map_expression(&Expression::ASpecCall {
          callee: Box::new(mapped_callee),
          args: mapped_args,
        })
      },
      Expression::ESpecCall{callee, args} => {
        let mapped_callee = callee.map(mapper);
        let mapped_args = args.iter().map(|arg| {
          arg.map(mapper)
        }).collect();
        mapper.map_expression(&Expression::ESpecCall {
          callee: Box::new(mapped_callee),
          args: mapped_args,
        })
      },
      Expression::Unop{expr, op} => {
        let mapped_expr = expr.map(mapper);
        mapper.map_expression(&Expression::Unop {
          expr: Box::new(mapped_expr),
          op: op.clone(),
        })
      },
      Expression::Binop{lhs, rhs, op} => {
        let mapped_lhs = lhs.map(mapper);
        let mapped_rhs = rhs.map(mapper);
        mapper.map_expression(&Expression::Binop {
          lhs: Box::new(mapped_lhs),
          rhs: Box::new(mapped_rhs),
          op: op.clone(),
        })
      },
      Expression::Forall{bindings, condition} => {
        let mapped_bindings = bindings.iter().map(|(v, t)| (mapper.map_name(v), t.clone())).collect();
        let mapped_condition = condition.map(mapper);
        mapper.map_expression(&Expression::Forall {
          bindings: mapped_bindings,
          condition: Box::new(mapped_condition),
        })
      },
      Expression::Statement(stmt) => {
        let mapped_stmt = stmt.map(mapper);
        mapper.map_expression(&Expression::Statement(Box::new(mapped_stmt)))
      },
    }
  }
}

impl BlockItem {
  pub fn map(&self, mapper: &mut dyn CRelMapper) -> BlockItem {
    match &self {
      BlockItem::Declaration(decl) => {
        let mapped_decl = decl.map(mapper);
        mapper.map_block_item(&BlockItem::Declaration(mapped_decl))
      },
      BlockItem::Statement(stmt) => {
        let mapped_stmt = stmt.map(mapper);
        mapper.map_block_item(&BlockItem::Statement(mapped_stmt))
      },
    }
  }
}
