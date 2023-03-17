use crate::crel::ast::*;

impl CRel {
  pub fn to_eggroll(&self) -> String {
    crel_to_eggroll(self)
  }
}

pub fn crel_to_eggroll(crel: &CRel) -> String {
  match crel {
    CRel::Declaration{specifiers, declarators} => {
      let spec_c = specifiers.iter()
        .map(declaration_specifier_to_eggroll)
        .collect::<Vec<String>>()
        .join(" ");
      let dec_c = declarators.iter()
        .map(init_declarator_to_eggroll)
        .collect::<Vec<String>>()
        .join(" ");
      format!("(declaration (specifiers {}) (declarators {}))", spec_c, dec_c)
    },
    CRel::FunctionDefinition{specifiers, name, params, body} => {
      let specs_egg = specifiers.iter()
        .map(declaration_specifier_to_eggroll)
        .collect::<Vec<String>>()
        .join(" ");
      let name_egg = declarator_to_eggroll(name);
      let args_egg = params.iter().map(declaration_to_eggroll).collect::<Vec<String>>().join(" ");
      let body_egg = statement_to_eggroll(body);
      format!("(fundef (specifiers {}) {} (params {}) (body {}))", specs_egg, name_egg, args_egg, body_egg)
    },
    CRel::Seq(crels) => {
      match crels.len() {
        0 => "".to_string(),
        1 => crel_to_eggroll(&crels[0]),
        _ => format!("(seq {} {})",
                     crel_to_eggroll(&crels[0]),
                     crel_to_eggroll(&CRel::Seq(crels[1..].to_vec())))
      }
    },
  }
}

fn expression_to_eggroll(expr: &Expression) -> String {
  match expr {
    Expression::Identifier{name} => name.clone(),
    Expression::ConstInt(i) => i.to_string(),
    Expression::StringLiteral(s) => format!("(lit-string {})", s.clone()),
    Expression::Call{callee, args} => {
      let callee_egg = expression_to_eggroll(callee);
      let args_egg = args.iter().map(expression_to_eggroll).collect::<Vec<String>>().join(" ");
      format!("(call {} (args {}))", callee_egg, args_egg)
    }
    Expression::Binop{ lhs, rhs, op } => match op {
      BinaryOp::Add    => format!("(+ {} {})",
                                  expression_to_eggroll(lhs), expression_to_eggroll(rhs)),
      BinaryOp::Assign => format!("(= {} {})",
                                  expression_to_eggroll(lhs), expression_to_eggroll(rhs)),
      BinaryOp::Sub    => format!("(- {} {})",
                                  expression_to_eggroll(lhs), expression_to_eggroll(rhs)),
      BinaryOp::Div    => format!("(/ {} {})",
                                  expression_to_eggroll(lhs), expression_to_eggroll(rhs)),
      BinaryOp::Equals => format!("(== {} {})",
                                  expression_to_eggroll(lhs), expression_to_eggroll(rhs)),
      BinaryOp::Lte    => format!("(<= {} {})",
                                  expression_to_eggroll(lhs), expression_to_eggroll(rhs)),
      BinaryOp::Mod    => format!("(mod {} {})",
                                  expression_to_eggroll(lhs), expression_to_eggroll(rhs)),
      BinaryOp::Mul    => format!("(* {} {})",
                                  expression_to_eggroll(lhs), expression_to_eggroll(rhs)),
    },
    Expression::Statement(stmt) => statement_to_eggroll(stmt),
  }
}

fn statement_to_eggroll(stmt: &Statement) -> String {
  match stmt {
    Statement::Compound(items) => {
      match items.len() {
        0 => "".to_string(),
        1 => block_item_to_eggroll(&items[0]),
        _ => format!("(seq {} {})",
                     block_item_to_eggroll(&items[0]),
                     statement_to_eggroll(&Statement::Compound(items[1..].to_vec())))
      }
    },
    Statement::Expression(expr) => expression_to_eggroll(expr),
    Statement::If{condition, then, els} => match els {
      None => format!("(if {} {})",
                      expression_to_eggroll(condition),
                      statement_to_eggroll(then)),
      Some(ebranch) => format!("(if {} {} {})",
                               expression_to_eggroll(condition),
                               statement_to_eggroll(then),
                               statement_to_eggroll(ebranch))
    },
    Statement::None => "".to_string(),
    Statement::Relation{ lhs, rhs } => {
      format!("(<|> {} {})", statement_to_eggroll(lhs), statement_to_eggroll(rhs))
    }
    Statement::Return(expr) => match expr {
      None => "return-none".to_string(),
      Some(ret) => format!("(return {})", expression_to_eggroll(ret)),
    },
    Statement::While{condition, body} => {
      format!("(while {} {})",
              expression_to_eggroll(condition),
              statement_to_eggroll(body))
    }
  }
}

fn declaration_specifier_to_eggroll(spec: &DeclarationSpecifier) -> String {
  match spec {
    DeclarationSpecifier::TypeSpecifier(ty) => format!("(type {})", type_to_eggroll(ty)),
  }
}

fn declarator_to_eggroll(dec: &Declarator) -> String {
  match dec {
    Declarator::Identifier{name} => name.clone(),
  }
}

fn init_declarator_to_eggroll(dec: &InitDeclarator) -> String {
  match &dec.expression {
    None => declarator_to_eggroll(&dec.declarator),
    Some(expr) => format!("(init-declarator {} {})",
                          declarator_to_eggroll(&dec.declarator),
                          expression_to_eggroll(&expr)),
  }
}

fn type_to_eggroll(ty: &Type) -> String {
  match ty {
    Type::Bool  => "bool".to_string(),
    Type::Float => "float".to_string(),
    Type::Int   => "int".to_string(),
    Type::Void  => "void".to_string(),
  }
}

fn declaration_to_eggroll(dec: &Declaration) -> String {
  let specs_egg = &dec.specifiers.iter()
    .map(declaration_specifier_to_eggroll)
    .collect::<Vec<String>>()
    .join(" ");
  let decs_egg = &dec.declarators.iter()
    .map(init_declarator_to_eggroll)
    .collect::<Vec<String>>()
    .join(" ");
  format!("(declaration (specifiers {}) (declarators {}))", specs_egg, decs_egg)
}

fn block_item_to_eggroll(item: &BlockItem) -> String {
  match item {
    BlockItem::Declaration(dec) => declaration_to_eggroll(dec),
    BlockItem::Statement(stmt)  => statement_to_eggroll(stmt),
  }
}
