use crate::crel::ast::*;
use lang_c::ast::*;
use lang_c::driver::{Config, parse};
use lang_c::span::Node;

/// Read the given C file and parse it into the RelC IR.
pub fn parse_crel(input_file: String) -> CRel {
  let config = Config::with_clang();
  let ast = match parse(&config, input_file) {
    Err(msg) => panic!("{}", msg),
    Ok(ast)  => ast,
  };
  CRel::Seq(ast.unit.0.into_iter()
    .map(trans_external_declaration)
    .collect())
}

fn trans_external_declaration(ext_decl: Node<ExternalDeclaration>) -> CRel {
  match ext_decl.node {
    ExternalDeclaration::Declaration(node) => trans_declaration(&node),
    ExternalDeclaration::StaticAssert(node) => CRel::Uninterp(format!("{:?}", node)),
    ExternalDeclaration::FunctionDefinition(node) => trans_function_definition(node),
  }
}

fn trans_declaration(decl: &Node<Declaration>) -> CRel {
  let specifiers = decl.node.specifiers.iter()
    .map(trans_declaration_specifier)
    .collect::<Vec<CRelSpecifier>>();
  let declarators = decl.node.declarators.iter()
    .map(trans_init_declarator)
    .collect::<Vec<CRel>>();
  CRel::Declaration{specifiers: specifiers, declarators: declarators}
}

fn trans_function_definition(def: Node<FunctionDefinition>) -> CRel {
  let specifiers = def.node.specifiers.iter()
    .map(trans_declaration_specifier)
    .collect::<Vec<CRelSpecifier>>();
  let declarator = trans_declarator(&def.node.declarator);
  let name = match declarator {
    CRel::Id(n) => n,
    _ => panic!("Unexpected function declarator: {:?}", declarator),
  };
  let declarations = def.node.declarations.iter()
    .map(trans_declaration)
    .collect::<Vec<CRel>>();
  let body = trans_statement(&def.node.statement);

  CRel::FunDef{
    specifiers: specifiers,
    name: name,
    args: declarations,
    body: Box::new(body),
  }
}

fn trans_declaration_specifier(decl_spec: &Node<DeclarationSpecifier>) -> CRelSpecifier {
  match &decl_spec.node {
    DeclarationSpecifier::StorageClass(node) => CRelSpecifier::Uninterp(format!("{:?}", node)),
    DeclarationSpecifier::TypeSpecifier(ts) => {
      let crel_type = trans_type_specifier(ts.node.clone());
      CRelSpecifier::TypeSpecifier(crel_type)
    }
    DeclarationSpecifier::TypeQualifier(node) => CRelSpecifier::Uninterp(format!("{:?}", node)),
    DeclarationSpecifier::Function(node) => CRelSpecifier::Uninterp(format!("{:?}", node)),
    DeclarationSpecifier::Alignment(node) => CRelSpecifier::Uninterp(format!("{:?}", node)),
    DeclarationSpecifier::Extension(node) => CRelSpecifier::Uninterp(format!("{:?}", node)),
  }
}

fn trans_declarator(decl: &Node<Declarator>) -> CRel {
  match &decl.node.kind.node {
    DeclaratorKind::Abstract => CRel::Uninterp(format!("{:?}", decl)),
    DeclaratorKind::Identifier(id) => CRel::Id(id.node.name.clone()),
    DeclaratorKind::Declarator(node_box) => trans_declarator(&*node_box),
  }
}

fn trans_init_declarator(decl: &Node<InitDeclarator>) -> CRel {
  let var = trans_declarator(&decl.node.declarator);
  let initializer = trans_initializer(&decl.node.initializer);
  match initializer {
    None => CRel::Init{ var: Box::new(var), val: None },
    Some(init) => CRel::Init{ var: Box::new(var), val: Some(Box::new(init)) },
  }

}

fn trans_initializer(initializer: &Option<Node<Initializer>>) -> Option<CRel> {
  match &initializer {
    None => None,
    Some(init) => Some( match &init.node {
      Initializer::Expression(expr) => trans_expression(&*expr),
      _ => CRel::Uninterp(format!("{:?}", init.node))
    })
  }
}

fn trans_type_specifier(type_spec: TypeSpecifier) -> CRelType {
  match type_spec {
    TypeSpecifier::Float => CRelType::Float,
    TypeSpecifier::Int   => CRelType::Int,
    TypeSpecifier::Void  => CRelType::Void,
    _ => CRelType::Uninterp(format!("{:?}", type_spec)),
  }
}

fn trans_statement(stmt: &Node<Statement>) -> CRel {
  match &stmt.node {
    Statement::Compound(items) => seq_with_rels(items.iter().map(trans_block_item).collect()),
    Statement::Expression(expr) => match expr {
      None => CRel::Skip,
      Some(expr) => trans_expression(expr),
    }
    Statement::Return(node) => match node {
      None => CRel::Skip,
      Some(expr) => CRel::Return(Box::new(trans_expression(expr))),
    }
    Statement::While(node) => trans_while_statement(&node),
    _ => CRel::Uninterp(format!("{:?}", stmt.node)),
  }
}

fn seq_with_rels(items: Vec<CRel>) -> CRel {
  let mut stack = Vec::new();
  let mut seq = Vec::new();
  for item in items {
    match &item {
      CRel::Call{ callee, args:_ } if callee == "rel_left" => {
        stack.push(seq);
        seq = Vec::new();
      },
      CRel::Call{ callee, args:_ } if callee == "rel_mid" => {
        stack.push(seq);
        seq = Vec::new();
      },
      CRel::Call{ callee, args:_ } if callee == "rel_right" => {
        let lhs = stack.pop().unwrap();
        let rhs = seq;
        seq = stack.pop().unwrap();
        seq.push(CRel::Rel{ lhs: Box::new(CRel::Seq(lhs)),
                            rhs: Box::new(CRel::Seq(rhs)) });
      },
      _ => seq.push(item),
    }
  };
  CRel::Seq(seq)
}

fn trans_expression(expr: &Node<Expression>) -> CRel {
  match &expr.node {
    Expression::BinaryOperator(node) => trans_binary_operator_expression(&*node),
    Expression::Call(call) => trans_call_expression(call),
    Expression::Constant(cnst) => trans_constant(&*cnst),
    Expression::Identifier(id) => CRel::Id(id.node.name.clone()),
    _ => CRel::Uninterp(format!("{:?}", expr.node)),
  }
}

fn trans_binary_operator_expression(expr: &Node<BinaryOperatorExpression>) -> CRel {
  let lhs = trans_expression(&*expr.node.lhs);
  let rhs = trans_expression(&*expr.node.rhs);
  trans_binary_operator(expr.node.operator.node.clone(), lhs, rhs)
}

fn trans_binary_operator(binop: BinaryOperator, lhs: CRel, rhs: CRel) -> CRel {
  match binop {
    BinaryOperator::Assign => CRel::Asgn{ lhs: Box::new(lhs), rhs: Box::new(rhs) },
    BinaryOperator::Equals => CRel::Eq(Box::new(lhs), Box::new(rhs)),
    BinaryOperator::LessOrEqual => CRel::Lte(Box::new(lhs), Box::new(rhs)),
    BinaryOperator::Plus => CRel::Add(Box::new(lhs), Box::new(rhs)),
    _ => panic!("Unsupported binary operator: {:?}", binop),
  }
}

fn trans_constant(cnst: &Node<Constant>) -> CRel {
  match &cnst.node {
    // Making some assumptions about base / suffix of integer here.
    Constant::Integer(i) => CRel::ConstInt(i.number.parse().unwrap()),
    _ => CRel::Uninterp(format!("{:?}", cnst.node)),
  }
}

fn trans_block_item(item: &Node<BlockItem>) -> CRel {
  match &item.node {
    BlockItem::Declaration(node) => trans_declaration(&node),
    BlockItem::Statement(node) => trans_statement(&node),
    _ => CRel::Uninterp(format!("{:?}", item.node)),
  }
}

fn trans_while_statement(expr: &Node<WhileStatement>) -> CRel {
  let cond = trans_expression(&expr.node.expression);
  let body = trans_statement(&*expr.node.statement);
  CRel::While { cond: Box::new(cond), body: Box::new(body) }
}

fn trans_call_expression(expr: &Node<CallExpression>) -> CRel {
  let callee = trans_expression(&*expr.node.callee);
  let args = expr.node.arguments.iter()
    .map(trans_expression)
    .collect();

  match callee {
    CRel::Id(name) => CRel::Call{ callee: name, args: args },
    _ => panic!("Unexpected callee: {:?}", callee),
  }

}
