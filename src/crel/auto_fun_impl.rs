use crate::crel::ast::*;
use uuid::Uuid;

/// A function implementation that computes and returns a hash of its inputs.
pub fn fun_impl_hash(fun_specifiers: &Vec<DeclarationSpecifier>,
                     fun_name: String,
                     fun_params: &Vec<ParameterDeclaration>) -> CRel {
  let hash_name = "hash".to_string();
  let hash_id: Expression = Expression::Identifier{name: hash_name.clone()};

  let mut body = vec![BlockItem::Declaration(Declaration {
    specifiers: vec![DeclarationSpecifier::TypeSpecifier(Type::Int)],
    declarator: Declarator::Identifier{name: hash_name.clone()},
    initializer: Some(Initializer::Expression(Expression::ConstInt(17))),
  })];

  let mut converted_params = Vec::new();
  let mut param_name_counter = 0;

  let update_hash = |expr: Expression| {
    let add_to_hash = Expression::Binop {
      op: BinaryOp::Add,
      lhs: Box::new(Expression::Binop {
        op: BinaryOp::Mul,
        lhs: Box::new(Expression::ConstInt(37)),
        rhs: Box::new(hash_id.clone()),
      }),
      rhs: Box::new(expr.clone()),
    };
    Expression::Binop {
      op: BinaryOp::Assign,
      lhs: Box::new(hash_id.clone()),
      rhs: Box::new(add_to_hash),
    }
  };

  for param in fun_params {
    match &param.declarator {
      None => {
        let name = format!("_p_{}", param_name_counter);
        param_name_counter += 1;
        converted_params.push(ParameterDeclaration {
          specifiers: param.specifiers.clone(),
          declarator: Some(Declarator::Identifier{name: name.clone()}),
        });
        body.push(BlockItem::Statement(Statement::Expression(Box::new(
          update_hash(Expression::Identifier{name: name.clone()})))));
      },
      Some(decl) => match decl {
        Declarator::Identifier{name} => {
          converted_params.push(param.clone());
          body.push(BlockItem::Statement(Statement::Expression(Box::new(
            update_hash(Expression::Identifier{name: name.clone()})))));
        },
        Declarator::Array { name, sizes } => {
          converted_params.push(param.clone());
          for size in sizes {
            let idx = format!("_i_{}", param_name_counter);
            let max_idx = format!("_i_{}_max", param_name_counter);
            param_name_counter += 1;
            body.push(BlockItem::Declaration(Declaration {
              declarator: Declarator::Identifier{name: idx.clone()},
              specifiers: vec!(DeclarationSpecifier::TypeSpecifier(Type::Int)),
              initializer: Some(Initializer::Expression(Expression::ConstInt(0))),
            }));
            body.push(BlockItem::Declaration(Declaration {
              declarator: Declarator::Identifier{name: max_idx.clone()},
              specifiers: vec!(DeclarationSpecifier::TypeSpecifier(Type::Int)),
              initializer: Some(Initializer::Expression(size.clone())),
            }));
            body.push(BlockItem::Statement(Statement::While {
              id: Uuid::new_v4(),
              runoff_link_id: None,
              invariants: Vec::new(),
              condition: Box::new(Expression::Binop {
                lhs: Box::new(Expression::Identifier{name: idx.clone()}),
                rhs: Box::new(Expression::Identifier{name: max_idx.clone()}),
                op: BinaryOp::Lt,
              }),
              body: Some(Box::new(Statement::Compound(vec!(
                BlockItem::Statement(Statement::Expression(Box::new(
                  update_hash(Expression::Binop {
                    lhs: Box::new(Expression::Identifier{name: name.clone()}),
                    rhs: Box::new(Expression::Identifier{name: idx.clone()}),
                    op: BinaryOp::Index,
                  })))),
                BlockItem::Statement(Statement::Expression(Box::new(Expression::Binop {
                  lhs: Box::new(Expression::Identifier{name: idx.clone()}),
                  rhs: Box::new(Expression::Binop {
                    lhs: Box::new(Expression::Identifier{name: idx.clone()}),
                    rhs: Box::new(Expression::ConstInt(1)),
                    op: BinaryOp::Add,
                  }),
                  op: BinaryOp::Assign,
                }))),
              )))),
              is_runoff: false,
              is_merged: false,
            }));
          }
        },
        _ => panic!("loop head paramameter declarator not supported: {:?}", decl),
      }
    }
  }
  body.push(BlockItem::Statement(Statement::Return(Some(Box::new(hash_id.clone())))));

  CRel::FunctionDefinition {
    specifiers: fun_specifiers.clone(),
    name: fun_name.clone(),
    params: converted_params,
    body: Box::new(Statement::Compound(body)),
  }
}
