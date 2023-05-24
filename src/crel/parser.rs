use crate::crel::ast::*;
use lang_c::ast as c;
use lang_c::driver::{Config, parse};
use lang_c::span::Node;

/// Read the given C file and parse it into the CRel IR.
pub fn parse_c_file(input_file: &String) -> CRel {
  let config = Config::with_clang();
  let ast = match parse(&config, input_file) {
    Err(msg) => panic!("{}", msg),
    Ok(ast)  => ast,
  };
  CRel::Seq(ast.unit.0.into_iter()
    .map(trans_external_declaration)
    .collect())
}

  /// Read the given C string and parse it into the CRel IR.
#[cfg(test)]
pub fn parse_c_string(input_str: String) -> CRel {
  let config = Config::with_clang();
  let parse = lang_c::driver::parse_preprocessed(&config, input_str);
  let ast = match parse {
    Err(msg) => panic!("{}", msg),
    Ok(ast)  => ast,
  };
  CRel::Seq(ast.unit.0.into_iter()
            .map(trans_external_declaration)
            .collect())
}

fn trans_external_declaration(ext_decl: Node<c::ExternalDeclaration>) -> CRel {
  match ext_decl.node {
    c::ExternalDeclaration::Declaration(decl) => {
      let specifiers = decl.node.specifiers.iter()
        .map(trans_declaration_specifier)
        .collect();
      let declarators = decl.node.declarators.iter()
        .map(trans_init_declarator)
        .collect();
      CRel::Declaration{specifiers, declarators}
    }
    c::ExternalDeclaration::FunctionDefinition(node) => trans_function_definition(node),
    _ => panic!("Unsupported external declaration: {:?}", ext_decl),
  }
}

fn trans_declaration(decl: &Node<c::Declaration>) -> Declaration {
  let specifiers = decl.node.specifiers.iter()
    .map(trans_declaration_specifier)
    .collect::<Vec<DeclarationSpecifier>>();
  let declarators = decl.node.declarators.iter()
    .map(trans_init_declarator)
    .collect::<Vec<InitDeclarator>>();
  Declaration{specifiers: specifiers, declarators: declarators}
}

fn trans_function_definition(def: Node<c::FunctionDefinition>) -> CRel {
  let specifiers = def.node.specifiers.iter()
    .map(trans_declaration_specifier)
    .collect::<Vec<DeclarationSpecifier>>();
  let declarator = trans_declarator(&def.node.declarator);
  let body = trans_statement(&def.node.statement);

  CRel::FunctionDefinition{specifiers, declarator, body: Box::new(body)}
}

fn trans_declaration_specifier(decl_spec: &Node<c::DeclarationSpecifier>) -> DeclarationSpecifier {
  match &decl_spec.node {
    c::DeclarationSpecifier::StorageClass(scs) => {
      let crel_spec = trans_storage_class_specifier(&scs.node);
      DeclarationSpecifier::StorageClass(crel_spec)
    }
    c::DeclarationSpecifier::TypeSpecifier(ts) => {
      let crel_type = trans_type_specifier(ts.node.clone());
      DeclarationSpecifier::TypeSpecifier(crel_type)
    }
    c::DeclarationSpecifier::TypeQualifier(ts) => {
      let crel_qual = trans_type_qualifier(ts.node.clone());
      DeclarationSpecifier::TypeQualifier(crel_qual)
    }
    _ => panic!("Unsupported declaration specifier: {:?}", decl_spec),
  }
}

fn trans_storage_class_specifier(sc_spec: &c::StorageClassSpecifier) -> StorageClassSpecifier {
  match sc_spec {
    c::StorageClassSpecifier::Extern => StorageClassSpecifier::Extern,
    _ => panic!("Unsupported storage class specifier: {:?}", sc_spec),
  }
}

fn trans_declarator(decl: &Node<c::Declarator>) -> Declarator {
  let name = match &decl.node.kind.node {
    c::DeclaratorKind::Identifier(id) => id.node.name.clone(),
    _ => panic!("Unsupported declarator: {:?}", decl),
  };
  let mut is_array = false;
  let mut array_size = None;
  let mut is_function = false;
  let mut function_params = None;
  let mut is_pointer = false;
  for derived in &decl.node.derived {
    match &derived.node {
      c::DerivedDeclarator::Array(array_decl) => match &array_decl.node.size {
        c::ArraySize::Unknown => is_array = true,
        c::ArraySize::VariableUnknown => is_array = true,
        c::ArraySize::VariableExpression(expr) => {
          is_array = true;
          array_size = Some(trans_expression(&*expr));
        },
        c::ArraySize::StaticExpression(expr) => {
          is_array = true;
          array_size = Some(trans_expression(&*expr));
        },
      },
      c::DerivedDeclarator::Function(fundecl) => {
        is_function = true;
        let params = fundecl.node.parameters.iter()
          .map(trans_parameter_declaration)
          .collect();
        function_params = Some(params);
      },
      c::DerivedDeclarator::Pointer(_) => {
        is_pointer = true;
      },
      _ => panic!("Unsupported derived declarator: {:?}", decl),
    };
  }

  let declarator = if is_array && is_function {
    panic!("Multiple derived declarators (array and function) not supported")
  } else if is_array {
    Declarator::Array{name, size: array_size}
  } else if is_function {
    Declarator::Function{name, params: function_params.unwrap_or(Vec::new())}
  } else {
    Declarator::Identifier{name}
  };

  if is_pointer {
    Declarator::Pointer(Box::new(declarator))
  } else {
    declarator
  }
}

fn trans_parameter_declaration(decl: &Node<c::ParameterDeclaration>) -> ParameterDeclaration {
  let specifiers = decl.node.specifiers.iter()
    .map(trans_declaration_specifier)
    .collect();
  let declarator = match &decl.node.declarator {
    None => None,
    Some(decl) => Some(trans_declarator(&decl)),
  };
  ParameterDeclaration{specifiers, declarator}
}

fn trans_init_declarator(decl: &Node<c::InitDeclarator>) -> InitDeclarator {
  let dec = trans_declarator(&decl.node.declarator);
  let init = trans_initializer(&decl.node.initializer);
  match init {
    None => InitDeclarator{ declarator: dec, expression: None },
    Some(init) => InitDeclarator{ declarator: dec, expression: Some(init) },
  }
}

fn trans_initializer(initializer: &Option<Node<c::Initializer>>) -> Option<Expression> {
  match &initializer {
    None => None,
    Some(init) => Some( match &init.node {
      c::Initializer::Expression(expr) => trans_expression(&*expr),
      _ => panic!("Unsupported initalizer: {:?}", init),
    })
  }
}

fn trans_type_specifier(type_spec: c::TypeSpecifier) -> Type {
  match type_spec {
    c::TypeSpecifier::Bool   => Type::Bool,
    c::TypeSpecifier::Double => Type::Double,
    c::TypeSpecifier::Float  => Type::Float,
    c::TypeSpecifier::Int    => Type::Int,
    c::TypeSpecifier::Void   => Type::Void,
    _ => panic!("Unsupported type specifier: {:?}", type_spec),
  }
}

fn trans_type_qualifier(type_qual: c::TypeQualifier) -> TypeQualifier {
  match type_qual {
    c::TypeQualifier::Const => TypeQualifier::Const,
    _ => panic!("Unsupported type qualifier: {:?}", type_qual),
  }
}

fn trans_statement(stmt: &Node<c::Statement>) -> Statement {
  match &stmt.node {
    c::Statement::Break => Statement::Break,
    c::Statement::Compound(items) => Statement::Compound(items.iter().map(trans_block_item).collect()),
    c::Statement::Expression(expr) => match expr {
      None => Statement::None,
      Some(expr) => Statement::Expression(Box::new(trans_expression(&*expr))),
    },
    c::Statement::If(stmt) => {
      let condition = Box::new(trans_expression(&stmt.node.condition));
      let then = Box::new(trans_statement(&stmt.node.then_statement));
      let els = match &stmt.node.else_statement {
        None => None,
        Some(else_stmt) => Some(Box::new(trans_statement(&else_stmt))),
      };
      Statement::If{condition, then, els}
    },
    c::Statement::Return(node) => match node {
      None => Statement::Return(None),
      Some(expr) => {
        let texpr = trans_expression(&expr);
        Statement::Return(Some(Box::new(texpr)))
      },
    },
    c::Statement::While(node) => trans_while_statement(&node),
    _ => panic!("Unsupported statement: {:?}", stmt),
  }
}

fn trans_expression(expr: &Node<c::Expression>) -> Expression {
  match &expr.node {
    c::Expression::UnaryOperator(unop) => {
      let expr = Box::new(trans_expression(&*unop.node.operand));
      let op = trans_unary_operator(&unop.node.operator.node);
      Expression::Unop{ expr, op }
    },
    c::Expression::BinaryOperator(binop) => {
      let lhs = Box::new(trans_expression(&*binop.node.lhs));
      let rhs = Box::new(trans_expression(&*binop.node.rhs));
      let op = trans_binary_operator(&binop.node.operator.node);
      Expression::Binop{ lhs, rhs, op }
    },
    c::Expression::Call(call) => trans_call_expression(call),
    c::Expression::Constant(cnst) => trans_constant(&*cnst),
    c::Expression::Identifier(id) => Expression::Identifier{ name: id.node.name.clone() },
    _ => panic!("Unsupported expression: {:?}", expr),
  }
}

fn trans_unary_operator(unop: &c::UnaryOperator) -> UnaryOp {
  match unop {
    c::UnaryOperator::Minus => UnaryOp::Minus,
    c::UnaryOperator::Negate => UnaryOp::Not,
    _ => panic!("Unsupported unary operator: {:?}", unop),
  }
}

fn trans_binary_operator(binop: &c::BinaryOperator) -> BinaryOp {
  match binop {
    c::BinaryOperator::Assign => BinaryOp::Assign,
    c::BinaryOperator::Equals => BinaryOp::Equals,
    c::BinaryOperator::Index => BinaryOp::Index,
    c::BinaryOperator::Greater => BinaryOp::Gt,
    c::BinaryOperator::GreaterOrEqual => BinaryOp::Gte,
    c::BinaryOperator::Less => BinaryOp::Lt,
    c::BinaryOperator::LessOrEqual => BinaryOp::Lte,
    c::BinaryOperator::LogicalAnd => BinaryOp::And,
    c::BinaryOperator::LogicalOr => BinaryOp::Or,
    c::BinaryOperator::Plus => BinaryOp::Add,
    c::BinaryOperator::Minus => BinaryOp::Sub,
    c::BinaryOperator::Multiply => BinaryOp::Mul,
    c::BinaryOperator::Divide => BinaryOp::Div,
    c::BinaryOperator::Modulo => BinaryOp::Mod,
    c::BinaryOperator::NotEquals => BinaryOp::NotEquals,
    _ => panic!("Unsupported binary operator: {:?}", binop),
  }
}

fn trans_constant(cnst: &Node<c::Constant>) -> Expression {
  match &cnst.node {
    // Making some assumptions about base / suffix of integer here.
    c::Constant::Integer(i) => Expression::ConstInt(i.number.parse().unwrap()),
    _ => panic!("Unsupported constant: {:?}", cnst),
  }
}

fn trans_block_item(item: &Node<c::BlockItem>) -> BlockItem {
  match &item.node {
    c::BlockItem::Declaration(node) => BlockItem::Declaration(trans_declaration(&node)),
    c::BlockItem::Statement(node) => BlockItem::Statement(trans_statement(&node)),
    _ => panic!("Unsupported block item: {:?}", item.node),
  }
}

fn trans_while_statement(expr: &Node<c::WhileStatement>) -> Statement {
  let condition = Box::new(trans_expression(&expr.node.expression));
  let body = match trans_statement(&*expr.node.statement) {
    Statement::None => None,
    stmt => Some(Box::new(stmt)),
  };
  Statement::While { condition, body }
}

fn trans_call_expression(expr: &Node<c::CallExpression>) -> Expression {
  let callee = trans_expression(&*expr.node.callee);
  let args = expr.node.arguments.iter()
    .map(trans_expression)
    .collect();
  Expression::Call{callee: Box::new(callee), args}
}
