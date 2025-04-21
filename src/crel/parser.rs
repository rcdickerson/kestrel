use crate::crel::ast::*;
use crate::spec::parser::bexpr;
use crate::spec::to_crel::*;
use lang_c::ast as c;
use lang_c::driver::{Config, parse};
use lang_c::span::Node;
use uuid::Uuid;

type ExprWithInvars = (Expression, Vec<Expression>);
type StmtWithInvars = (Statement,  Vec<Expression>);

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
      let declarations = trans_declaration(&decl).iter()
        .map(|decl| CRel::Declaration(decl.clone()))
        .collect();
      CRel::Seq(declarations)
    },
    c::ExternalDeclaration::FunctionDefinition(node) => {
      trans_function_definition(&node)
    },
    _ => panic!("Unsupported external declaration: {:?}", ext_decl),
  }
}

fn trans_declaration(decl: &Node<c::Declaration>) -> Vec<Declaration> {
 let specifiers: Vec<DeclarationSpecifier> = decl.node.specifiers.iter()
    .map(trans_declaration_specifier)
    .collect();
  decl.node.declarators.iter()
    .map(trans_init_declarator)
    .map(|(declarator, initializer)| {
      Declaration{specifiers: specifiers.clone(), declarator, initializer}
    }).collect()
}

fn trans_function_definition(def: &Node<c::FunctionDefinition>) -> CRel {
  let specifiers = def.node.specifiers.iter()
    .map(trans_declaration_specifier)
    .collect::<Vec<DeclarationSpecifier>>();
  let declarator = trans_declarator(&def.node.declarator);
  let (name, params) = declarator.expect_function();
  let (body, _) = trans_statement(&def.node.statement);
  CRel::FunctionDefinition {
    specifiers,
    name: name.clone(),
    params: params.clone(),
    body: Box::new(body)
  }
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
  let mut array_sizes = Vec::new();
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
          array_sizes.push(trans_expression(expr).0);
        },
        c::ArraySize::StaticExpression(expr) => {
          is_array = true;
          array_sizes.push(trans_expression(expr).0);
        },
      },
      c::DerivedDeclarator::Function(fundecl) => {
        is_function = true;
        let params = fundecl.node.parameters.iter()
          .map(trans_parameter_declaration)
          .collect();
        function_params = Some(params);
      },
      c::DerivedDeclarator::KRFunction(_) => {
        is_function = true;
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
    Declarator::Array{name, sizes: array_sizes}
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
  let declarator = decl.node.declarator.as_ref().map(trans_declarator);
  ParameterDeclaration{specifiers, declarator}
}

fn trans_init_declarator(decl: &Node<c::InitDeclarator>) -> (Declarator, Option<Initializer>) {
  let dec = trans_declarator(&decl.node.declarator);
  let init = decl.node.initializer.as_ref().map(|init| {
    trans_initializer(init)
  });
  (dec, init)
}

fn trans_initializer(initializer: &Node<c::Initializer>) -> Initializer {
  match &initializer.node {
    c::Initializer::Expression(expr) => {
      Initializer::Expression(trans_expression(expr).0)
    },
    c::Initializer::List(exprs) => {
      Initializer::List(exprs.into_iter()
                        .map(|item| trans_initializer(&item.node.initializer))
                        .collect())
    }
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

fn trans_statement(stmt: &Node<c::Statement>) -> StmtWithInvars {
  match &stmt.node {
    c::Statement::Break => (Statement::Break, Vec::new()),
    c::Statement::Compound(items) => {
      let mut stmts = Vec::new();
      let mut invs = Vec::new();
      for item in items {
        let (mut stmt, mut inv) = trans_block_item(item);
        stmts.append(&mut stmt);
        invs.append(&mut inv);
      }
      (Statement::Compound(stmts), invs)
    },
    c::Statement::Expression(expr) => match expr {
      None => (Statement::None, Vec::new()),
      Some(expr) => {
        let (expr, invars) = trans_expression(expr);
        (Statement::Expression(Box::new(expr)), invars)
      },
    },
    c::Statement::If(stmt) => {
      let condition = Box::new(trans_expression(&stmt.node.condition).0);
      let (then, mut invs) = trans_statement(&stmt.node.then_statement);
      let (els, mut einvs) = match &stmt.node.else_statement {
        None => (None, Vec::new()),
        Some(stmt) => {
          let (s, i) = trans_statement(&stmt);
          (Some(Box::new(s)), i)
        },
      };
      invs.append(&mut einvs);
      (Statement::If{condition, then: Box::new(then), els }, invs)
    },
    c::Statement::Return(node) => match node {
      None => (Statement::Return(None), Vec::new()),
      Some(expr) => {
        let (texpr, invars) = trans_expression(expr);
        (Statement::Return(Some(Box::new(texpr))), invars)
      },
    },
    c::Statement::While(node) => (trans_while_statement(node), Vec::new()),
    _ => panic!("Unsupported statement: {:?}", stmt),
  }
}

fn trans_expression(expr: &Node<c::Expression>) -> ExprWithInvars {
  match &expr.node {
    c::Expression::UnaryOperator(unop) => {
      let (expr, invars) = trans_expression(&unop.node.operand);
      let op = trans_unary_operator(&unop.node.operator.node);
      (Expression::Unop{ expr: Box::new(expr), op }, invars)
    },
    c::Expression::BinaryOperator(binop) => {
      let (lhs, mut invars) = trans_expression(&binop.node.lhs);
      let (rhs, mut rinvars) = trans_expression(&binop.node.rhs);
      let op = trans_binary_operator(&binop.node.operator.node);
      invars.append(&mut rinvars);
      (Expression::Binop{ lhs: Box::new(lhs), rhs: Box::new(rhs), op }, invars)
    },
    c::Expression::Call(call) => trans_call_expression(call),
    c::Expression::Constant(cnst) => (trans_constant(cnst), Vec::new()),
    c::Expression::Identifier(id) =>
      (Expression::Identifier{ name: id.node.name.clone() }, Vec::new()),
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
    c::Constant::Float(f) => Expression::ConstFloat(f.number.parse().unwrap()),
    _ => panic!("Unsupported constant: {:?}", cnst),
  }
}

fn trans_block_item(item: &Node<c::BlockItem>) -> (Vec<BlockItem>, Vec<Expression>) {
  match &item.node {
    c::BlockItem::Declaration(node) => {
      let decl = trans_declaration(node).iter().map(|decl| {
        BlockItem::Declaration(decl.clone())
      }).collect();
      (decl, Vec::new())
    },
    c::BlockItem::Statement(node) => {
      let (stmt, invars) = trans_statement(node);
      if stmt.is_none() {
        (Vec::new(), invars)
      } else {
        (vec!(BlockItem::Statement(stmt)), invars)
      }
    },
    _ => panic!("Unsupported block item: {:?}", item.node),
  }
}

fn trans_while_statement(expr: &Node<c::WhileStatement>) -> Statement {
  let condition = Box::new(trans_expression(&expr.node.expression).0);
  let (stmt, invars) = trans_statement(&expr.node.statement);
  let body = if stmt.is_none() { None } else { Some(Box::new(stmt)) };
  Statement::While {
    id: Uuid::new_v4(),
    runoff_link_id: None,
    is_runoff: false,
    is_merged: false,
    invariants: invars,
    condition,
    body
  }
}

fn trans_call_expression(expr: &Node<c::CallExpression>) -> ExprWithInvars {
  let (callee, invars) = trans_expression(&expr.node.callee);
  match callee {
    Expression::Identifier{name} if name == "_invariant" => {
      let invars = expr.node.arguments.iter()
        .map(|arg| match &arg.node {
          c::Expression::StringLiteral(lit) => {
            let mut chars = lit.node[0].chars();
            chars.next();      // Remove leading and trailing
            chars.next_back(); // quotation marks.
            chars.as_str()
          }
          _ => panic!("Expecting string arguments to _invariant"),
        })
        .map(|invar_str| match bexpr(invar_str) {
          Ok((_, expr)) => expr.to_crel(),
          Err(err) => panic!("Error parsing invariant: {}", err),
        })
        .collect();
      (Expression::Statement(Box::new(Statement::None)), invars)
    },
    Expression::Identifier{name} if name == "assert" && expr.node.arguments.len() == 1 => {
      (Expression::Statement(Box::new(Statement::Assert(
        Box::new(trans_bexp(&expr.node.arguments[0]))
      ))), invars)
    },
    Expression::Identifier{name} if name == "assume" && expr.node.arguments.len() == 1 => {
      (Expression::Statement(Box::new(Statement::Assume(
        Box::new(trans_bexp(&expr.node.arguments[0]))
      ))), invars)
    },
    _ => {
      let args = expr.node.arguments.iter()
        .map(|arg| trans_expression(arg).0)
        .collect();
      (Expression::Call{callee: Box::new(callee), args}, invars)
    },
  }
}

fn trans_bexp(c_expr: &Node<c::Expression>) -> Expression {
  match trans_expression(c_expr).0 {
    Expression::ConstInt(0) => Expression::ConstBool(false),
    Expression::ConstInt(_) => Expression::ConstBool(true),
    crel_expr => crel_expr,
  }
}
