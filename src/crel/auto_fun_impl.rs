use crate::crel::ast::*;

/// A function implementation that computes and returns a hash of its inputs.
pub fn fun_impl_hash(fun_specifiers: &Vec<DeclarationSpecifier>,
                     fun_name: String,
                     fun_params: &Vec<ParameterDeclaration>) -> CRel {
  let hash_name = "hash".to_string();
  let hash_id: Expression = Expression::Identifier{name: hash_name.clone()};

  let mut body = vec![BlockItem::Declaration(Declaration {
    specifiers: vec![DeclarationSpecifier::TypeSpecifier(Type::Int)],
    declarator: Declarator::Identifier{name: hash_name.clone()},
    initializer: Some(Expression::ConstInt(17)),
  })];

  let mut converted_params = Vec::new();
  let mut param_name_counter = 0;
  for param in fun_params {
    let param_name = match &param.declarator {
      None => {
        let name = format!("_p_{}", param_name_counter);
        converted_params.push(ParameterDeclaration {
          specifiers: param.specifiers.clone(),
          declarator: Some(Declarator::Identifier{name: name.clone()}),
        });
        param_name_counter += 1;
        name
      },
      Some(decl) => match decl {
        Declarator::Identifier{name} => {
          converted_params.push(param.clone());
          name.clone()
        },
        _ => panic!("loop head paramameter declarator not supported: {:?}", decl),
      }
    };
    let updated_hash = Expression::Binop {
      op: BinaryOp::Add,
      lhs: Box::new(Expression::Binop {
        op: BinaryOp::Mul,
        lhs: Box::new(Expression::ConstInt(37)),
        rhs: Box::new(hash_id.clone()),
      }),
      rhs: Box::new(Expression::Identifier{name: param_name}),
    };
    body.push(BlockItem::Statement(Statement::Expression(Box::new(Expression::Binop {
      op: BinaryOp::Assign,
      lhs: Box::new(hash_id.clone()),
      rhs: Box::new(updated_hash),
    }))));
  }
  body.push(BlockItem::Statement(Statement::Return(Some(Box::new(hash_id.clone())))));

  CRel::FunctionDefinition {
    specifiers: fun_specifiers.clone(),
    name: fun_name.clone(),
    params: converted_params,
    body: Box::new(Statement::Compound(body)),
  }
}
