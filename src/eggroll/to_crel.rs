use crate::crel::ast::*;
use sexp::{Atom, Sexp};

pub fn eggroll_to_crel(eggroll: &String) -> CRel {
  match sexp::parse(eggroll.as_str()) {
    Err(msg) => panic!("{}", msg),
    Ok(sexp) => expect_crel(&sexp),
  }
}

fn expect_crel(sexp: &Sexp) -> CRel {
  match &sexp {
    Sexp::Atom(Atom::S(s)) if s.is_empty() => CRel::Seq(Vec::new()),
    Sexp::List(sexps) => match &sexps[0] {
      Sexp::Atom(Atom::S(s)) if s == "declaration" => {
        let declaration = expect_declaration(&sexps[1]);
        CRel::Declaration(declaration)
      },
      Sexp::Atom(Atom::S(s)) if s == "fundef" => {
        let specifiers = expect_specifiers(&sexps[1]);
        let name = expect_string(&sexps[2]);
        let params = expect_param_decls(&sexps[3]);
        let body = Box::new(expect_statement(&sexps[4]));
        CRel::FunctionDefinition{specifiers, name, params, body}
      },
      Sexp::Atom(Atom::S(s)) if s == "seq" => {
        let mut seq = vec!(expect_crel(&sexps[1]));
        let rhs = expect_crel(&sexps[2]);
        match rhs {
          CRel::Seq(crels) => seq.append(&mut crels.to_owned()),
          _ => seq.push(rhs),
        };
        CRel::Seq(seq)
      },
      _ => panic!("Expected CRel s-expression, got: {}", sexp),
    },
    _ => panic!("Expected CRel s-expression, got: {}", sexp),
  }
}

fn expect_expression(sexp: &Sexp) -> Expression {
  match &sexp {
    Sexp::Atom(Atom::S(s)) if !s.is_empty() => Expression::Identifier{name: s.clone()},
    Sexp::List(sexps) => match &sexps[0] {
      Sexp::Atom(Atom::S(s)) if s == "lit-string" => {
        Expression::StringLiteral(expect_string(&sexps[1]))
      },
      Sexp::Atom(Atom::S(s)) if s == "const-int" => {
        match &sexps[1] {
          Sexp::Atom(Atom::I(i)) => Expression::ConstInt(i32::try_from(i.clone()).unwrap()),
          _ => panic!("Cannot convert to integer from {:?}", sexps[1]),
        }
      },
      Sexp::Atom(Atom::S(s)) if s == "const-float" => {
        match &sexps[1] {
          Sexp::Atom(Atom::S(s)) => Expression::ConstFloat(s.parse().unwrap()),
          _ => panic!("Cannot convert to integer from {:?}", sexps[1]),
        }
      },
      Sexp::Atom(Atom::S(s)) if s == "neg" => {
        let expr = Box::new(expect_expression(&sexps[1]));
        Expression::Unop{ expr, op: UnaryOp::Minus }
      },
      Sexp::Atom(Atom::S(s)) if s == "not" => {
        let expr = Box::new(expect_expression(&sexps[1]));
        Expression::Unop{ expr, op: UnaryOp::Not }
      },
      Sexp::Atom(Atom::S(s)) if s == "call" => {
        let callee = Box::new(expect_expression(&sexps[1]));
        let args = expect_args(&sexps[2]);
        Expression::Call{ callee, args }
      },
      Sexp::Atom(Atom::S(s)) if s == "index" => {
        let lhs = Box::new(expect_expression(&sexps[1]));
        let rhs = Box::new(expect_expression(&sexps[2]));
        Expression::Binop{ lhs, rhs, op: BinaryOp::Index }
      },
      Sexp::Atom(Atom::S(s)) if s == "+" => {
        let lhs = Box::new(expect_expression(&sexps[1]));
        let rhs = Box::new(expect_expression(&sexps[2]));
        Expression::Binop{ lhs, rhs, op: BinaryOp::Add }
      },
      Sexp::Atom(Atom::S(s)) if s == "&&" => {
        let lhs = Box::new(expect_expression(&sexps[1]));
        let rhs = Box::new(expect_expression(&sexps[2]));
        Expression::Binop{ lhs, rhs, op: BinaryOp::And }
      },
      Sexp::Atom(Atom::S(s)) if s == "=" => {
        let lhs = Box::new(expect_expression(&sexps[1]));
        let rhs = Box::new(expect_expression(&sexps[2]));
        Expression::Binop{ lhs, rhs, op: BinaryOp::Assign }
      },
      Sexp::Atom(Atom::S(s)) if s == "-" => {
        let lhs = Box::new(expect_expression(&sexps[1]));
        let rhs = Box::new(expect_expression(&sexps[2]));
        Expression::Binop{ lhs, rhs, op: BinaryOp::Sub }
      },
      Sexp::Atom(Atom::S(s)) if s == "/" => {
        let lhs = Box::new(expect_expression(&sexps[1]));
        let rhs = Box::new(expect_expression(&sexps[2]));
        Expression::Binop{ lhs, rhs, op: BinaryOp::Div }
      },
      Sexp::Atom(Atom::S(s)) if s == "==" => {
        let lhs = Box::new(expect_expression(&sexps[1]));
        let rhs = Box::new(expect_expression(&sexps[2]));
        Expression::Binop{ lhs, rhs, op: BinaryOp::Equals }
      },
      Sexp::Atom(Atom::S(s)) if s == ">" => {
        let lhs = Box::new(expect_expression(&sexps[1]));
        let rhs = Box::new(expect_expression(&sexps[2]));
        Expression::Binop{ lhs, rhs, op: BinaryOp::Gt }
      },
      Sexp::Atom(Atom::S(s)) if s == ">=" => {
        let lhs = Box::new(expect_expression(&sexps[1]));
        let rhs = Box::new(expect_expression(&sexps[2]));
        Expression::Binop{ lhs, rhs, op: BinaryOp::Gte }
      },
      Sexp::Atom(Atom::S(s)) if s == "<" => {
        let lhs = Box::new(expect_expression(&sexps[1]));
        let rhs = Box::new(expect_expression(&sexps[2]));
        Expression::Binop{ lhs, rhs, op: BinaryOp::Lt }
      },
      Sexp::Atom(Atom::S(s)) if s == "<=" => {
        let lhs = Box::new(expect_expression(&sexps[1]));
        let rhs = Box::new(expect_expression(&sexps[2]));
        Expression::Binop{ lhs, rhs, op: BinaryOp::Lte }
      },
      Sexp::Atom(Atom::S(s)) if s == "mod" => {
        let lhs = Box::new(expect_expression(&sexps[1]));
        let rhs = Box::new(expect_expression(&sexps[2]));
        Expression::Binop{ lhs, rhs, op: BinaryOp::Mod }
      },
      Sexp::Atom(Atom::S(s)) if s == "*" => {
        let lhs = Box::new(expect_expression(&sexps[1]));
        let rhs = Box::new(expect_expression(&sexps[2]));
        Expression::Binop{ lhs, rhs, op: BinaryOp::Mul }
      },
      Sexp::Atom(Atom::S(s)) if s == "!=" => {
        let lhs = Box::new(expect_expression(&sexps[1]));
        let rhs = Box::new(expect_expression(&sexps[2]));
        Expression::Binop{ lhs, rhs, op: BinaryOp::NotEquals }
      },
      Sexp::Atom(Atom::S(s)) if s == "||" => {
        let lhs = Box::new(expect_expression(&sexps[1]));
        let rhs = Box::new(expect_expression(&sexps[2]));
        Expression::Binop{ lhs, rhs, op: BinaryOp::Or }
      },
      _ => Expression::Statement(Box::new(expect_statement(sexp))),
    },
    _ => Expression::Statement(Box::new(expect_statement(sexp))),
  }
}

fn expect_statement(sexp: &Sexp) -> Statement {
  match &sexp {
    Sexp::Atom(Atom::S(s)) if s == "break" => Statement::Break,
    Sexp::Atom(Atom::S(s)) if s == "return-none" => Statement::Return(None),
    Sexp::List(sexps) => match &sexps[0] {
      Sexp::Atom(Atom::S(s)) if s == "basic-block" => {
        let items = sexps[1..].iter()
          .map(expect_block_item)
          .collect();
        Statement::BasicBlock(items)
      },
      Sexp::Atom(Atom::S(s)) if s == "seq" => {
        let mut seq = vec!(expect_block_item(&sexps[1]));
        let rhs = expect_statement(&sexps[2]);
        match rhs {
            Statement::Compound(items) => {
            seq.append(&mut items.to_owned())
          },
          _ => seq.push(BlockItem::Statement(rhs)),
        };
        Statement::Compound(seq)
      },
      Sexp::Atom(Atom::S(s)) if s == "if" => {
        let condition = Box::new(expect_expression(&sexps[1]));
        let then = Box::new(expect_statement(&sexps[2]));
        Statement::If{condition, then, els: None}
      },
      Sexp::Atom(Atom::S(s)) if s == "if-else" => {
        let condition = Box::new(expect_expression(&sexps[1]));
        let then = Box::new(expect_statement(&sexps[2]));
        let els  = Some(Box::new(expect_statement(&sexps[3])));
        Statement::If{condition, then, els}
      },
      Sexp::Atom(Atom::S(s)) if s == "<|>" => {
        let lhs = Box::new(expect_statement(&sexps[1]));
        let rhs = Box::new(expect_statement(&sexps[2]));
        Statement::Relation{lhs, rhs}
      },
      Sexp::Atom(Atom::S(s)) if s == "|>" => {
        let lhs = Box::new(Statement::None);
        let rhs = Box::new(expect_statement(&sexps[1]));
        Statement::Relation{lhs, rhs}
      },
      Sexp::Atom(Atom::S(s)) if s == "<|" => {
        let lhs = Box::new(expect_statement(&sexps[1]));
        let rhs = Box::new(Statement::None);
        Statement::Relation{lhs, rhs}
      },
      Sexp::Atom(Atom::S(s)) if s == "declaration" => {
        Statement::Compound(vec!(BlockItem::Declaration(expect_declaration(sexp))))
      },
      Sexp::Atom(Atom::S(s)) if s == "return" => {
        Statement::Return(Some(Box::new(expect_expression(&sexps[1]))))
      },
      Sexp::Atom(Atom::S(s)) if s == "while-no-body" => {
        let condition = Box::new(expect_expression(&sexps[1]));
        Statement::While{condition, body: None}
      },
      Sexp::Atom(Atom::S(s)) if s == "while" => {
        let condition = Box::new(expect_expression(&sexps[1]));
        let body = Some(Box::new(expect_statement(&sexps[2])));
        Statement::While{condition, body}
      },
      Sexp::Atom(Atom::S(s)) if s == "while-double" => {
        let condition = expect_expression(&sexps[1]);
        let body_stmt = expect_statement(&sexps[2]);
        let double_body = Statement::Compound(vec!(
          BlockItem::Statement(body_stmt.clone()),
          BlockItem::Statement(Statement::If {
            condition: Box::new(condition.clone()),
            then: Box::new(body_stmt.clone()),
            els: None,
          }),
        ));
        Statement::While {
          condition: Box::new(condition),
          body: Some(Box::new(double_body))
        }
      },
      Sexp::Atom(Atom::S(s)) if s == "while-lockstep" => {
        let cond1 = expect_expression(&sexps[1]);
        let cond2 = expect_expression(&sexps[2]);
        let conj = Expression::Binop {
          lhs: Box::new(cond1.clone()),
          rhs: Box::new(cond2.clone()),
          op: BinaryOp::And,
        };
        let runoff_cond1 = Expression::Binop {
          lhs: Box::new(cond1.clone()),
          rhs: Box::new(Expression::Unop{
            expr: Box::new(cond2.clone()),
            op: UnaryOp::Not}),
          op: BinaryOp::And,
        };
        let runoff_cond2 = Expression::Binop {
          lhs: Box::new(Expression::Unop{
            expr: Box::new(cond1.clone()),
            op: UnaryOp::Not}),
          rhs: Box::new(cond2.clone()),
          op: BinaryOp::And,
        };

        let runoff_body1 = expect_statement(&sexps[3]);
        let runoff_body2 = expect_statement(&sexps[4]);
        let body = expect_statement(&sexps[5]);

        let stmts = vec! [
          BlockItem::Statement(Statement::While {
            condition: Box::new(conj),
            body: Some(Box::new(body))}),
          BlockItem::Statement(Statement::While {
            condition: Box::new(runoff_cond1),
            body: Some(Box::new(runoff_body1))}),
          BlockItem::Statement(Statement::While {
            condition: Box::new(runoff_cond2),
            body: Some(Box::new(runoff_body2))}),
        ];
        Statement::Compound(stmts)
      },
      Sexp::Atom(Atom::S(s)) if s == "while-scheduled" => {
        expect_while_scheduled(&sexps)
      },
      _ => Statement::Expression(Box::new(expect_expression(&sexp)))
    },
    _ => Statement::Expression(Box::new(expect_expression(&sexp)))
  }
}

fn expect_while_scheduled(sexps: &[Sexp]) -> Statement {
  let left_iters = expect_i64(&sexps[1]);
  let right_iters = expect_i64(&sexps[2]);
  let cond1 = expect_expression(&sexps[3]);
  let cond2 = expect_expression(&sexps[4]);
  let conj = Expression::Binop {
    lhs: Box::new(cond1.clone()),
    rhs: Box::new(cond2.clone()),
    op: BinaryOp::And,
  };
  let runoff1 = Expression::Binop {
    lhs: Box::new(cond1.clone()),
    rhs: Box::new(Expression::Unop{
      expr: Box::new(cond2.clone()),
      op: UnaryOp::Not}),
    op: BinaryOp::And,
  };
  let runoff2 = Expression::Binop {
    lhs: Box::new(Expression::Unop{
      expr: Box::new(cond1.clone()),
      op: UnaryOp::Not}),
    rhs: Box::new(cond2.clone()),
    op: BinaryOp::And,
  };

  let body1 = expect_statement(&sexps[5]);
  let mut body1_rel = body1.clone();
  let mut repeats1 = vec!(body1.clone());
  while (repeats1.len() as i64) < left_iters {
    let next_iter = Statement::If {
      condition: Box::new(cond1.clone()),
      then: Box::new(body1.clone()),
      els: None,
    };
    repeats1.push(next_iter);
  }
  if left_iters > 1 {
    let items = repeats1.iter()
      .map(|s| BlockItem::Statement(s.clone()))
      .collect();
    body1_rel = Statement::Compound(items);
  }

  let body2 = expect_statement(&sexps[6]);
  let mut body2_rel = body2.clone();
  let mut repeats2 = vec!(body2.clone());
  while (repeats2.len() as i64) < right_iters {
    let next_iter = Statement::If {
      condition: Box::new(cond2.clone()),
      then: Box::new(body2.clone()),
      els: None,
    };
    repeats2.push(next_iter);
  }
  if right_iters > 1 {
    let items = repeats2.iter()
      .map(|s| BlockItem::Statement(s.clone()))
      .collect();
    body2_rel = Statement::Compound(items);
  }

  let bodies = Statement::Relation {
    lhs: Box::new(body1_rel),
    rhs: Box::new(body2_rel),
  };

  let stmts = vec! [
    BlockItem::Statement(Statement::While {
      condition: Box::new(conj),
      body: Some(Box::new(bodies))}),
    BlockItem::Statement(Statement::While {
      condition: Box::new(runoff1),
      body: Some(Box::new(body1))}),
    BlockItem::Statement(Statement::While {
      condition: Box::new(runoff2),
      body: Some(Box::new(body2))}),
  ];
  Statement::Compound(stmts)
}

fn expect_specifiers(sexp: &Sexp) -> Vec<DeclarationSpecifier> {
  match &sexp {
    Sexp::Atom(Atom::S(s)) if s == "specifiers" => Vec::new(),
    Sexp::List(sexps) => match &sexps[0] {
      Sexp::Atom(Atom::S(s)) if s == "specifiers" => {
        sexps[1..].iter()
          .map(expect_declaration_specifier)
          .collect()
      },
      _ => panic!("Expected declaration specifiers, got: {}", sexp),
    }
    _ => panic!("Expected declaration specifiers, got: {}", sexp),
  }
}

fn expect_declaration_specifier(sexp: &Sexp) -> DeclarationSpecifier {
  match &sexp {
    Sexp::List(sexps) => match &sexps[0] {
      Sexp::Atom(Atom::S(s)) if s == "storage-class" => {
        DeclarationSpecifier::StorageClass(expect_storage_class_specifier(&sexps[1]))
      }
      Sexp::Atom(Atom::S(s)) if s == "type" => {
        DeclarationSpecifier::TypeSpecifier(expect_type(&sexps[1]))
      }
      Sexp::Atom(Atom::S(s)) if s == "type-qualifier" => {
        DeclarationSpecifier::TypeQualifier(expect_type_qualifier(&sexps[1]))
      }
      _ => panic!("Expected declaration specifier, got: {}", sexp),
    },
    _ => panic!("Expected declaration specifier, got: {}", sexp),
  }
}

fn expect_type(sexp: &Sexp) -> Type {
  match &sexp {
    Sexp::Atom(Atom::S(ty)) => match ty.as_str() {
      "bool" => Type::Bool,
      "double" => Type::Double,
      "float" => Type::Float,
      "int" => Type::Int,
      "void" => Type::Void,
      _ => panic!("Unknown type: {}", ty),
    },
    _ => panic!("Expected type, got: {}", sexp)
  }
}

fn expect_type_qualifier(sexp: &Sexp) -> TypeQualifier {
  match &sexp {
    Sexp::Atom(Atom::S(ty)) => match ty.as_str() {
      "const" => TypeQualifier::Const,
      _ => panic!("Unknown type qualifier: {}", ty),
    },
    _ => panic!("Expected type qualifier, got: {}", sexp)
  }
}

fn expect_storage_class_specifier(sexp: &Sexp) -> StorageClassSpecifier {
  match &sexp {
    Sexp::Atom(Atom::S(scs)) => match scs.as_str() {
      "extern" => StorageClassSpecifier::Extern,
      _ => panic!("Expected storage class specifier, got: {}", scs),
    },
    _ => panic!("Expected storage class specifier, got: {}", sexp),
  }
}

fn expect_declaration(sexp: &Sexp) -> Declaration {
  match &sexp {
    Sexp::List(sexps) => match &sexps[0] {
      Sexp::Atom(Atom::S(s)) if s == "declaration" => {
        let specifiers = expect_specifiers(&sexps[1]);
        let declarator = expect_declarator(&sexps[2]);
        let initializer = expect_initializer(&sexps[3]);
        Declaration{specifiers, declarator, initializer}
      },
      _ => panic!("Expected declaration, got: {}", sexp),
    },
    _ => panic!("Expected declaration, got: {}", sexp),
  }
}

fn expect_initializer(sexp: &Sexp) -> Option<Expression> {
  match &sexp {
    Sexp::Atom(Atom::S(s)) if s == "initializer" => None,
    Sexp::List(sexps) => match &sexps[0] {
      Sexp::Atom(Atom::S(s)) if s == "initializer" => {
        let expr = expect_expression(&sexps[1]);
        Some(expr)
      },
      _ => panic!("Expected initializer, got: {}", sexp),
    },
    _ => panic!("Expected initializer, got: {}", sexp),
  }
}

fn expect_declarator(sexp: &Sexp) -> Declarator {
  match &sexp {
    Sexp::Atom(Atom::S(name)) => Declarator::Identifier{name: name.clone()},
    Sexp::List(sexps) => match &sexps[0] {
      Sexp::Atom(Atom::S(s)) if s == "unsized-array" => {
        Declarator::Array{name: expect_string(&sexps[1]), sizes: Vec::new()}
      },
      Sexp::Atom(Atom::S(s)) if s == "sized-array" => {
        let sizes = expect_array_sizes(&sexps[2]);
        Declarator::Array{name: expect_string(&sexps[1]), sizes: sizes}
      },
      Sexp::Atom(Atom::S(s)) if s == "fun-declarator" => {
        let params = expect_param_decls(&sexps[2]);
        Declarator::Function{name: expect_string(&sexps[1]), params}
      },
      Sexp::Atom(Atom::S(s)) if s == "pointer" => {
        let decl = expect_declarator(&sexps[1]);
        Declarator::Pointer(Box::new(decl))
      },
      _ => panic!("Expected declarator, got: {}", sexp),
    }
    _ => panic!("Expected declarator, got: {}", sexp),
  }
}

fn expect_array_sizes(sexp: &Sexp) -> Vec<Expression> {
 match &sexp {
    Sexp::Atom(Atom::S(s)) if s == "array-sizes" => Vec::new(),
    Sexp::List(sexps) => match &sexps[0] {
      Sexp::Atom(Atom::S(s)) if s == "array-sizes" => {
        sexps[1..].iter()
          .map(expect_expression)
          .collect()
      },
      _ => panic!("Expected array sizes, got: {}", sexp),
    },
    _ => panic!("Expected array sizes, got: {}", sexp),
  }
}

fn expect_param_decls(sexp: &Sexp) -> Vec<ParameterDeclaration> {
  match &sexp {
    Sexp::Atom(Atom::S(s)) if s == "params" => Vec::new(),
    Sexp::List(sexps) => match &sexps[0] {
      Sexp::Atom(Atom::S(s)) if s == "params" => {
        sexps[1..].iter()
          .map(expect_param_declaration)
          .collect()
      },
      _ => panic!("Expected params, got: {}", sexp),
    },
    _ => panic!("Expected params, got: {}", sexp),
  }
}

fn expect_param_declaration(sexp: &Sexp) -> ParameterDeclaration {
  match &sexp {
    Sexp::List(sexps) => match &sexps[0] {
      Sexp::Atom(Atom::S(s)) if s == "param-declaration" => {
        let specifiers = expect_specifiers(&sexps[1]);
        let declarator = if *&sexps.len() > 2 {
          Some(expect_declarator(&sexps[2]))
        } else { None };
        ParameterDeclaration{specifiers, declarator}
      },
      _ => panic!("Expected declaration, got: {}", sexp),
    },
    _ => panic!("Expected params, got: {}", sexp),
  }
}

fn expect_args(sexp: &Sexp) -> Vec<Expression> {
  match &sexp {
    Sexp::Atom(Atom::S(s)) if s == "args" => Vec::new(),
    Sexp::List(sexps) => match &sexps[0] {
      Sexp::Atom(Atom::S(s)) if s == "args" => {
        sexps[1..].iter()
          .map(expect_expression)
          .collect()
      },
      _ => panic!("Expected args, got: {}", sexp),
    },
    _ => panic!("Expected args, got: {}", sexp),
  }
}

fn expect_block_item(sexp: &Sexp) -> BlockItem {
  match &sexp {
    Sexp::List(sexps) => match &sexps[0] {
      Sexp::Atom(Atom::S(s)) if s == "declaration" => {
        let declaration = expect_declaration(sexp);
        BlockItem::Declaration(declaration)
      },
      _ => BlockItem::Statement(expect_statement(&sexp)),
    },
    _ => BlockItem::Statement(expect_statement(&sexp)),
  }
}

fn expect_string(sexp: &Sexp) -> String {
  match &sexp {
    Sexp::Atom(Atom::S(s)) => s.clone(),
    _ => panic!("Expected string literal, got: {}", sexp)
  }
}

fn expect_i64(sexp: &Sexp) -> i64 {
  match &sexp {
    Sexp::Atom(Atom::I(i)) => *i,
    _ => panic!("Expected i64, got: {}", sexp)
  }
}
