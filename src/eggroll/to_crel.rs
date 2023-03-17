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
        let specifiers = expect_specifiers(&sexps[1]);
        let declarators = expect_init_declarators(&sexps[2]);
        CRel::Declaration{specifiers, declarators}
      },
      Sexp::Atom(Atom::S(s)) if s == "fundef" => {
        let specifiers = expect_specifiers(&sexps[1]);
        let name = expect_declarator(&sexps[2]);
        let params = expect_params(&sexps[3]);
        let body = Box::new(expect_body(&sexps[4]));
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
    Sexp::Atom(Atom::I(i)) => Expression::ConstInt(i32::try_from(i.clone()).unwrap()),
    Sexp::List(sexps) => match &sexps[0] {
      Sexp::Atom(Atom::S(s)) if s == "lit-string" => {
        Expression::StringLiteral(expect_string(&sexps[1]))
      },
      Sexp::Atom(Atom::S(s)) if s == "call" => {
        let callee = Box::new(expect_expression(&sexps[1]));
        let args = expect_args(&sexps[2]);
        Expression::Call{callee, args}
      },
      Sexp::Atom(Atom::S(s)) if s == "+" => {
        let lhs = Box::new(expect_expression(&sexps[1]));
        let rhs = Box::new(expect_expression(&sexps[2]));
        Expression::Binop{lhs, rhs, op: BinaryOp::Add}
      },
      Sexp::Atom(Atom::S(s)) if s == "=" => {
        let lhs = Box::new(expect_expression(&sexps[1]));
        let rhs = Box::new(expect_expression(&sexps[2]));
        Expression::Binop{lhs, rhs, op: BinaryOp::Assign}
      },
      Sexp::Atom(Atom::S(s)) if s == "-" => {
        let lhs = Box::new(expect_expression(&sexps[1]));
        let rhs = Box::new(expect_expression(&sexps[2]));
        Expression::Binop{lhs, rhs, op: BinaryOp::Sub}
      },
      Sexp::Atom(Atom::S(s)) if s == "/" => {
        let lhs = Box::new(expect_expression(&sexps[1]));
        let rhs = Box::new(expect_expression(&sexps[2]));
        Expression::Binop{lhs, rhs, op: BinaryOp::Div}
      },
      Sexp::Atom(Atom::S(s)) if s == "==" => {
        let lhs = Box::new(expect_expression(&sexps[1]));
        let rhs = Box::new(expect_expression(&sexps[2]));
        Expression::Binop{lhs, rhs, op: BinaryOp::Equals}
      },
      Sexp::Atom(Atom::S(s)) if s == "<=" => {
        let lhs = Box::new(expect_expression(&sexps[1]));
        let rhs = Box::new(expect_expression(&sexps[2]));
        Expression::Binop{lhs, rhs, op: BinaryOp::Lte}
      },
      Sexp::Atom(Atom::S(s)) if s == "mod" => {
        let lhs = Box::new(expect_expression(&sexps[1]));
        let rhs = Box::new(expect_expression(&sexps[2]));
        Expression::Binop{lhs, rhs, op: BinaryOp::Mod}
      },
      Sexp::Atom(Atom::S(s)) if s == "*" => {
        let lhs = Box::new(expect_expression(&sexps[1]));
        let rhs = Box::new(expect_expression(&sexps[2]));
        Expression::Binop{lhs, rhs, op: BinaryOp::Mul}
      },
      _ => Expression::Statement(Box::new(expect_statement(sexp))),
    },
    _ => Expression::Statement(Box::new(expect_statement(sexp))),
  }
}

fn expect_statement(sexp: &Sexp) -> Statement {
  match &sexp {
    Sexp::Atom(Atom::S(s)) if s == "return-none" => Statement::Return(None),
    Sexp::List(sexps) => match &sexps[0] {
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
        let els  =
          if sexps.len() > 3 {
            Some(Box::new(expect_statement(&sexps[3])))
          } else { None };
        Statement::If{condition, then, els}
      },
      Sexp::Atom(Atom::S(s)) if s == "<|>" => {
        let lhs = Box::new(expect_statement(&sexps[1]));
        let rhs = Box::new(expect_statement(&sexps[2]));
        Statement::Relation{lhs, rhs}
      },
      Sexp::Atom(Atom::S(s)) if s == "declaration" => {
        Statement::Compound(vec!(BlockItem::Declaration(expect_declaration(sexp))))
      },
      Sexp::Atom(Atom::S(s)) if s == "return" => {
        Statement::Return(Some(Box::new(expect_expression(&sexps[1]))))
      },
      Sexp::Atom(Atom::S(s)) if s == "while" => {
        let condition = Box::new(expect_expression(&sexps[1]));
        let body = Box::new(expect_statement(&sexps[2]));
        Statement::While{condition, body}
      },
      _ => Statement::Expression(Box::new(expect_expression(&sexp)))
    },
    _ => Statement::Expression(Box::new(expect_expression(&sexp)))
  }
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
      Sexp::Atom(Atom::S(s)) if s == "type" => {
        DeclarationSpecifier::TypeSpecifier(expect_type(&sexps[1]))
      },
      _ => panic!("Expected declaration specifier, got: {}", sexp),
    },
    _ => panic!("Expected declaration specifier, got: {}", sexp),
  }
}

fn expect_type(sexp: &Sexp) -> Type {
  match &sexp {
    Sexp::Atom(Atom::S(ty)) => match ty.as_str() {
      "bool" => Type::Bool,
      "float" => Type::Float,
      "int" => Type::Int,
      "void" => Type::Void,
      _ => panic!("Unknown type: {}", ty),
    },
    _ => panic!("Expected type, got: {}", sexp)
  }
}

fn expect_init_declarators(sexp: &Sexp) -> Vec<InitDeclarator> {
  match &sexp {
    Sexp::List(sexps) => match &sexps[0] {
      Sexp::Atom(Atom::S(s)) if s == "declarators" => {
        sexps[1..].iter()
          .map(expect_init_declarator)
          .collect()
      },
      _ => panic!("Expected declarators, got: {}", sexp),
    },
    _ => panic!("Expected declarators, got: {}", sexp),
  }
}

fn expect_init_declarator(sexp: &Sexp) -> InitDeclarator {
  match &sexp {
    Sexp::List(sexps) => match &sexps[0] {
      Sexp::Atom(Atom::S(s)) if s == "init-declarator" => {
        let declarator = expect_declarator(&sexps[1]);
        let expression = Some(expect_expression(&sexps[2]));
        InitDeclarator{ declarator, expression }
      },
      _ => InitDeclarator{ declarator: expect_declarator(sexp), expression: None }
    },
    _ => InitDeclarator{ declarator: expect_declarator(sexp), expression: None }
  }
}

fn expect_declarator(sexp: &Sexp) -> Declarator {
  match &sexp {
    Sexp::Atom(Atom::S(name)) => Declarator::Identifier{ name: name.clone() },
    _ => panic!("Expected declarator, got: {}", sexp),
  }
}

fn expect_params(sexp: &Sexp) -> Vec<Declaration> {
  match &sexp {
    Sexp::Atom(Atom::S(s)) if s == "params" => Vec::new(),
    Sexp::List(sexps) => match &sexps[0] {
      Sexp::Atom(Atom::S(s)) if s == "params" => {
        sexps[1..].iter()
          .map(expect_declaration)
          .collect()
      },
      _ => panic!("Expected params, got: {}", sexp),
    },
    _ => panic!("Expected params, got: {}", sexp),
  }
}

fn expect_declaration(sexp: &Sexp) -> Declaration {
  match &sexp {
    Sexp::List(sexps) => match &sexps[0] {
      Sexp::Atom(Atom::S(s)) if s == "declaration" => {
        let specifiers = expect_specifiers(&sexps[1]);
        let declarators = expect_init_declarators(&sexps[2]);
        Declaration{specifiers, declarators}
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

fn expect_body(sexp: &Sexp) -> Statement {
  match &sexp {
    Sexp::List(sexps) => match &sexps[0] {
      Sexp::Atom(Atom::S(s)) if s == "body" => {
        expect_statement(&sexps[1])
      },
      _ => panic!("Expected body, got: {}", sexp),
    },
    _ => panic!("Expected body, got: {}", sexp),
  }
}

fn expect_block_item(sexp: &Sexp) -> BlockItem {
  match &sexp {
    Sexp::List(sexps) => match &sexps[0] {
      Sexp::Atom(Atom::S(s)) if s == "declaration" => {
        let specifiers = expect_specifiers(&sexps[1]);
        let declarators = expect_init_declarators(&sexps[2]);
        BlockItem::Declaration(Declaration{specifiers, declarators})
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
