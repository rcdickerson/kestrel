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
    CRel::FunctionDefinition{specifiers, declarator, body} => {
      let specs_egg = specifiers.iter()
        .map(declaration_specifier_to_eggroll)
        .collect::<Vec<String>>()
        .join(" ");
      let declarator_egg = declarator_to_eggroll(declarator);
      let body_egg = statement_to_eggroll(body);
      format!("(fundef (specifiers {}) {} {})", specs_egg, declarator_egg, body_egg)
    },
    CRel::Seq(crels) => {
      match crels.len() {
        0 => "()".to_string(),
        1 => crel_to_eggroll(&crels[0]),
        _ => {
          let first = crel_to_eggroll(&crels[0]);
          let rest = crel_to_eggroll(&CRel::Seq(crels[1..].to_vec()));
          format!("(seq {} {})", first, rest)
        }
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
    },
    Expression::Unop{ expr, op } => match op {
      UnaryOp::Minus => format!("(neg {})", expression_to_eggroll(expr)),
      UnaryOp::Not => format!("(not {})", expression_to_eggroll(expr)),
    },
    Expression::Binop{ lhs, rhs, op } => match op {
      BinaryOp::Add       => format!("(+ {} {})",
                                     expression_to_eggroll(lhs), expression_to_eggroll(rhs)),
      BinaryOp::And       => format!("(&& {} {})",
                                     expression_to_eggroll(lhs), expression_to_eggroll(rhs)),
      BinaryOp::Assign    => format!("(= {} {})",
                                     expression_to_eggroll(lhs), expression_to_eggroll(rhs)),
      BinaryOp::Sub       => format!("(- {} {})",
                                     expression_to_eggroll(lhs), expression_to_eggroll(rhs)),
      BinaryOp::Div       => format!("(/ {} {})",
                                     expression_to_eggroll(lhs), expression_to_eggroll(rhs)),
      BinaryOp::Equals    => format!("(== {} {})",
                                     expression_to_eggroll(lhs), expression_to_eggroll(rhs)),
      BinaryOp::Gt        => format!("(> {} {})",
                                     expression_to_eggroll(lhs), expression_to_eggroll(rhs)),
      BinaryOp::Gte       => format!("(>= {} {})",
                                     expression_to_eggroll(lhs), expression_to_eggroll(rhs)),
      BinaryOp::Index     => format!("(index {} {})",
                                     expression_to_eggroll(lhs), expression_to_eggroll(rhs)),
      BinaryOp::Lt        => format!("(< {} {})",
                                     expression_to_eggroll(lhs), expression_to_eggroll(rhs)),
      BinaryOp::Lte       => format!("(<= {} {})",
                                     expression_to_eggroll(lhs), expression_to_eggroll(rhs)),
      BinaryOp::Mod       => format!("(mod {} {})",
                                     expression_to_eggroll(lhs), expression_to_eggroll(rhs)),
      BinaryOp::Mul       => format!("(* {} {})",
                                     expression_to_eggroll(lhs), expression_to_eggroll(rhs)),
      BinaryOp::NotEquals => format!("(!= {} {})",
                                     expression_to_eggroll(lhs), expression_to_eggroll(rhs)),
      BinaryOp::Or        => format!("(|| {} {})",
                                     expression_to_eggroll(lhs), expression_to_eggroll(rhs)),
    },
    Expression::Statement(stmt) => statement_to_eggroll(stmt),
  }
}

fn statement_to_eggroll(stmt: &Statement) -> String {
  match stmt {
    Statement::BasicBlock(items) => {
      let items_eggroll = items.iter()
        .map(block_item_to_eggroll)
        .collect::<Vec<String>>()
        .join(" ");
      format!("(basic-block {})", items_eggroll)
    },
    Statement::Break => "break".to_string(),
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
      Some(ebranch) => format!("(if-else {} {} {})",
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
      match body {
        None => format!("(while-no-body {})", expression_to_eggroll(condition)),
        Some(stmt) => format!("(while {} {})",
                              expression_to_eggroll(condition),
                              statement_to_eggroll(stmt)),
      }
    }
  }
}

fn declaration_specifier_to_eggroll(spec: &DeclarationSpecifier) -> String {
  match spec {
    DeclarationSpecifier::StorageClass(scs) => {
      format!("(storage-class {})", storage_class_specifier_to_eggroll(scs))
    }
    DeclarationSpecifier::TypeSpecifier(ty) => {
      format!("(type {})", type_to_eggroll(ty))
    }
    DeclarationSpecifier::TypeQualifier(tq) => {
      format!("(type-qualifier {})", type_qualifier_to_eggroll(tq))
    }
  }
}

fn declarator_to_eggroll(dec: &Declarator) -> String {
  match dec {
    Declarator::Identifier{name} => name.clone(),
    Declarator::Array{name, size} => {
      match &size {
        None => format!("(unized-array {})", name.clone()),
        Some(expr) => {
          let size_egg = expression_to_eggroll(expr);
          format!("(sized-array {} {})", name.clone(), size_egg)
        }
      }
    },
    Declarator::Function{name, params} => {
      let params_egg = params.iter().map(param_decl_to_eggroll).collect::<Vec<String>>().join(" ");
      format!("(fun-declarator {} (params {}))", name.clone(), params_egg)
    },
    Declarator::Pointer(decl) => {
      let decl_egg = declarator_to_eggroll(decl);
      format!("(pointer {})", decl_egg)
    },
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
    Type::Bool   => "bool".to_string(),
    Type::Double => "double".to_string(),
    Type::Float  => "float".to_string(),
    Type::Int    => "int".to_string(),
    Type::Void   => "void".to_string(),
  }
}

fn type_qualifier_to_eggroll(tq: &TypeQualifier) -> String {
  match tq {
    TypeQualifier::Const => "const".to_string(),
  }
}

fn storage_class_specifier_to_eggroll(scs: &StorageClassSpecifier) -> String {
  match scs {
    StorageClassSpecifier::Extern => "extern".to_string(),
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

fn param_decl_to_eggroll(dec: &ParameterDeclaration) -> String {
  let specs_egg = &dec.specifiers.iter()
    .map(declaration_specifier_to_eggroll)
    .collect::<Vec<String>>()
    .join(" ");
  let dec_egg = match &dec.declarator {
    None => "".to_string(),
    Some(decl) => declarator_to_eggroll(decl),
  };
  format!("(declaration (specifiers {}) {})", specs_egg, dec_egg)
}

fn block_item_to_eggroll(item: &BlockItem) -> String {
  match item {
    BlockItem::Declaration(dec) => declaration_to_eggroll(dec),
    BlockItem::Statement(stmt)  => statement_to_eggroll(stmt),
  }
}
