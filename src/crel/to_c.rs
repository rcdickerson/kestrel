use crate::crel::ast::*;
use crate::shanty as C;

impl CRel {
  pub fn to_c(&self) -> String {
    let mut source = C::Source::new();
    source.include("seahorn/seahorn.h");
    crel_to_c(self, &mut source);
    source.to_string()
  }
}

fn crel_to_c(crel: &CRel, source: &mut C::Source) {
  match crel {
    CRel::Declaration{specifiers, declarators} => {
      source.declare_variable(&var_to_c(specifiers, declarators));
    },
    CRel::FunctionDefinition{specifiers, name, params, body} => {
      source.push_function(&fun_to_c(specifiers, name, params, body));
    },
    CRel::Seq(seq) => {
      for crel in seq { crel_to_c(crel, source) }
    }
  }
}

fn var_to_c(specifiers: &Vec<DeclarationSpecifier>, declarators: &Vec<InitDeclarator>) -> C::Variable {
  let mut var_name = None;
  let mut var_ty = None;
  let mut var_val = None;
  let mut var_extern = false;
  for spec in specifiers {
    match spec {
      DeclarationSpecifier::StorageClass(sc_spec) => {
        match sc_spec {
          StorageClassSpecifier::Extern => var_extern = true,
        }
      },
      DeclarationSpecifier::TypeSpecifier(ts) => {
        var_ty = Some(type_to_c(ts));
      }
    }
  }
  for decl in declarators {
    match &decl.declarator {
      Declarator::Identifier{name} => var_name = Some(name),
    }
    match &decl.expression {
      None => (),
      Some(expr) => {
        var_val = Some(expression_to_c(&expr));
      }
    }
  }
  let mut var = C::Variable::new(
    var_name.expect("Variable declaration has no name"),
    var_ty.expect("Variable declaration has no type"));
  var.set_extern(var_extern);
  match var_val {
    None => (),
    Some(expr) => { var.set_value(&expr); },
  }
  var
}

fn fun_to_c(specifiers: &Vec<DeclarationSpecifier>,
            name: &Declarator,
            params: &Vec<Declaration>,
            body: &Statement) -> C::Function {

  let name = match name {
    Declarator::Identifier{name} => name,
  };

  let mut fun_ty = C::Type::Void;
  let mut fun_extern = false;
  for spec in specifiers {
    match spec {
      DeclarationSpecifier::StorageClass(sc_spec) => {
        match sc_spec {
          StorageClassSpecifier::Extern => fun_extern = true,
        }
      },
      DeclarationSpecifier::TypeSpecifier(ts) => {
        fun_ty = type_to_c(ts);
      }
    }
  }

  let mut fun = C::Function::new(name, fun_ty);
  for param in params.iter().map(decl_to_param) {
    fun.push_param(&param);
  }
  fun.set_extern(fun_extern);
  fun.set_body(&statement_to_c(body));
  fun
}

fn decl_to_param(decl: &Declaration) -> C::FunctionParameter {
  let mut param_name = None;
  let mut param_ty = None;
  for spec in &decl.specifiers {
    match spec {
      DeclarationSpecifier::StorageClass(sc_spec) => {
        match sc_spec {
          StorageClassSpecifier::Extern => panic!("Cannot have an extern param")
        }
      },
      DeclarationSpecifier::TypeSpecifier(ts) => {
        param_ty = Some(type_to_c(&ts));
      }
    }
  }
  for decl in &decl.declarators {
    match &decl.declarator {
      Declarator::Identifier{name} => param_name = Some(name),
    }
    match &decl.expression {
      None => (),
      Some(_) => panic!("Cannot give param a value"),
    }
  }
  C::FunctionParameter::new(
    param_name.expect("Parameter has no name"),
    param_ty.expect("Parameter has no type"))
}

fn expression_to_c(expr: &Expression) -> C::Expression {
  match expr {
    Expression::Identifier{name} => C::Expression::Identifier {
      name: name.clone(),
    },
    Expression::ConstInt(i) => C::Expression::ConstInt(*i),
    Expression::StringLiteral(s) => C::Expression::StringLiteral(s.clone()),
    Expression::Call{ callee, args } => {
      C::Expression::FnCall {
        name: Box::new(expression_to_c(callee)),
        args: args.iter()
          .map(expression_to_c)
          .collect::<Vec<C::Expression>>(),
      }
    },
    Expression::Unop{ expr, op } => {
      let expr = Box::new(expression_to_c(expr));
      let op = match op {
        UnaryOp::Minus => "-".to_string(),
        UnaryOp::Not   => "!".to_string(),
      };
      C::Expression::UnOp{expr, op}
    },
    Expression::Binop{ lhs, rhs, op } => {
      let lhs = Box::new(expression_to_c(lhs));
      let rhs = Box::new(expression_to_c(rhs));
      match op {
        BinaryOp::Add       => C::Expression::BinOp{lhs, rhs, op: "+".to_string()},
        BinaryOp::And       => C::Expression::BinOp{lhs, rhs, op: "&&".to_string()},
        BinaryOp::Assign    => C::Expression::BinOp{lhs, rhs, op: "=".to_string()},
        BinaryOp::Sub       => C::Expression::BinOp{lhs, rhs, op: "-".to_string()},
        BinaryOp::Div       => C::Expression::BinOp{lhs, rhs, op: "/".to_string()},
        BinaryOp::Equals    => C::Expression::BinOp{lhs, rhs, op: "==".to_string()},
        BinaryOp::Gt        => C::Expression::BinOp{lhs, rhs, op: ">".to_string()},
        BinaryOp::Gte       => C::Expression::BinOp{lhs, rhs, op: ">=".to_string()},
        BinaryOp::Index     => C::Expression::ArrayIndex{expr: lhs, index: rhs},
        BinaryOp::Lt        => C::Expression::BinOp{lhs, rhs, op: "<".to_string()},
        BinaryOp::Lte       => C::Expression::BinOp{lhs, rhs, op: "<=".to_string()},
        BinaryOp::Mod       => C::Expression::BinOp{lhs, rhs, op: "%".to_string()},
        BinaryOp::Mul       => C::Expression::BinOp{lhs, rhs, op: "*".to_string()},
        BinaryOp::NotEquals => C::Expression::BinOp{lhs, rhs, op: "!=".to_string()},
        BinaryOp::Or        => C::Expression::BinOp{lhs, rhs, op: "||".to_string()},
      }
    },
    Expression::Statement(stmt) => {
      C::Expression::Statement(Box::new(statement_to_c(stmt)))
    },
  }
}

fn statement_to_c(stmt: &Statement) -> C::Statement {
  match stmt {
    Statement::BasicBlock(items) => {
      C::Statement::Seq(items.iter().map(block_item_to_c).collect())
    },
    Statement::Break => C::Statement::Break,
    Statement::Compound(items) => {
      C::Statement::Seq(items.iter().map(block_item_to_c).collect())
    },
    Statement::Expression(expr) => {
      C::Statement::Expression(Box::new(expression_to_c(expr)))
    },
    Statement::If{condition, then, els} => {
      C::Statement::If {
        condition: Box::new(expression_to_c(condition)),
        then: Box::new(statement_to_c(then)),
        els: match els {
          None => None,
          Some(stmt) => Some(Box::new(statement_to_c(stmt))),
        }
      }
    },
    Statement::None => C::Statement::Seq(Vec::new()),
    Statement::Relation{ lhs, rhs } => {
      C::Statement::Seq(vec!(statement_to_c(lhs), statement_to_c(rhs)))
    }
    Statement::Return(expr) => match expr {
      None => { C::Statement::Return(None) },
      Some(ret) => { C::Statement::Return(Some(Box::new(expression_to_c(ret)))) },
    },
    Statement::While{condition, body} => {
      let condition = Box::new(expression_to_c(condition));
      let body = match body {
        None => None,
        Some(stmt) => { Some(Box::new(statement_to_c(stmt))) }
      };
      C::Statement::While{condition, body}
    }
  }
}

fn block_item_to_c(item: &BlockItem) -> C::Statement {
  match item {
    BlockItem::Declaration(dec) => {
      C::Statement::Variable(var_to_c(&dec.specifiers, &dec.declarators))
    },
    BlockItem::Statement(stmt) => statement_to_c(stmt),
  }
}

fn type_to_c(ty: &Type) -> C::Type {
  match ty {
    Type::Bool   => C::Type::Bool,
    Type::Double => C::Type::Double,
    Type::Float  => C::Type::Float,
    Type::Int    => C::Type::Int,
    Type::Void   => C::Type::Void,
  }
}
