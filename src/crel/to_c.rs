use crate::crel::ast::*;

impl CRel {
  pub fn to_c(&self) -> String {
    crel_to_c(self)
  }
}

fn crel_to_c(crel: &CRel) -> String {
  match crel {
    CRel::Declaration{specifiers, declarators} => {
      let spec_c = declaration_specifiers_to_c(specifiers);
      let dec_c = init_declarators_to_c(declarators);
      format!("{} {}", spec_c, dec_c)
    },
    CRel::FunctionDefinition{specifiers, name, params, body} => {
      let spec_c = declaration_specifiers_to_c(specifiers);
      let name_c = declarator_to_c(name);
      let args_c = params.iter()
        .map(declaration_to_c)
        .collect::<Vec<String>>()
        .join(", ");
      let body_c = statement_to_c(body);
      format!("{} {}({}) {{\n{}\n}}", spec_c, name_c, args_c, body_c)
    },
    CRel::Seq(seq) => {
      format!("{};", seq.iter().map(crel_to_c).collect::<Vec<String>>().join(";\n"))
    }
  }
}

fn expression_to_c(expr: &Expression) -> String {
  match expr {
    Expression::Identifier{name} => name.clone(),
    Expression::ConstInt(i) => i.to_string(),
    Expression::StringLiteral(s) => s.clone(),
    Expression::Call{ callee, args } => {
      let callee_c = expression_to_c(callee);
      let args_c = args.iter()
        .map(expression_to_c)
        .collect::<Vec<String>>()
        .join(", ");
      format!("{}({})", callee_c, args_c)
    },
    Expression::Unop{ expr, op } => match op {
      UnaryOp::Minus => format!("-({})", expression_to_c(expr)),
      UnaryOp::Not => format!("!({})", expression_to_c(expr)),
    },
    Expression::Binop{ lhs, rhs, op } => match op {
      BinaryOp::Add       => format!("({}) + ({})", expression_to_c(lhs), expression_to_c(rhs)),
      BinaryOp::And       => format!("({}) && ({})", expression_to_c(lhs), expression_to_c(rhs)),
      BinaryOp::Assign    => format!("({}) = ({})", expression_to_c(lhs), expression_to_c(rhs)),
      BinaryOp::Sub       => format!("({}) - ({})", expression_to_c(lhs), expression_to_c(rhs)),
      BinaryOp::Div       => format!("({}) / ({})", expression_to_c(lhs), expression_to_c(rhs)),
      BinaryOp::Equals    => format!("({}) == ({})", expression_to_c(lhs), expression_to_c(rhs)),
      BinaryOp::Gt        => format!("({}) > ({})", expression_to_c(lhs), expression_to_c(rhs)),
      BinaryOp::Gte       => format!("({}) >= ({})", expression_to_c(lhs), expression_to_c(rhs)),
      BinaryOp::Index     => format!("{}[{}]", expression_to_c(lhs), expression_to_c(rhs)),
      BinaryOp::Lt        => format!("({}) < ({})", expression_to_c(lhs), expression_to_c(rhs)),
      BinaryOp::Lte       => format!("({}) <= ({})", expression_to_c(lhs), expression_to_c(rhs)),
      BinaryOp::Mod       => format!("({}) % ({})", expression_to_c(lhs), expression_to_c(rhs)),
      BinaryOp::Mul       => format!("({}) * ({})", expression_to_c(lhs), expression_to_c(rhs)),
      BinaryOp::NotEquals => format!("({}) != ({})", expression_to_c(lhs), expression_to_c(rhs)),
      BinaryOp::Or        => format!("({}) || ({})", expression_to_c(lhs), expression_to_c(rhs)),
    },
    Expression::Statement(stmt) => statement_to_c(stmt),
  }
}

fn statement_to_c(stmt: &Statement) -> String {
  match stmt {
    Statement::BasicBlock(items) => {
      format!("{};", items.iter().map(block_item_to_c).collect::<Vec<String>>().join(";\n"))
    },
    Statement::Break => "break".to_string(),
    Statement::Compound(items) => {
      format!("{};", items.iter().map(block_item_to_c).collect::<Vec<String>>().join(";\n"))
    },
    Statement::Expression(expr) => expression_to_c(expr),
    Statement::If{condition, then, els} => match els {
      None => format!("if( {} ) {{\n{}\n}}",
                      expression_to_c(condition),
                      statement_to_c(then)),
      Some(ebranch) => format!("if( {} ) {{\n{}\n}} else {{\n{}\n}}",
                               expression_to_c(condition),
                               statement_to_c(then),
                               statement_to_c(ebranch))
    },
    Statement::None => "".to_string(),
    Statement::Relation{ lhs, rhs } => {
      format!("{}\n{}", statement_to_c(lhs), statement_to_c(rhs))
    }
    Statement::Return(expr) => match expr {
      None => "return".to_string(),
      Some(ret) => format!("return {}", expression_to_c(ret)),
    },
    Statement::While{condition, body} => {
      match body {
        None => format!("while ({})",  expression_to_c(condition)),
        Some(stmt) => format!("while ({}) {{\n{}\n}}",
                              expression_to_c(condition),
                              statement_to_c(stmt)),
      }
    }
  }
}

fn block_item_to_c(item: &BlockItem) -> String {
  match item {
    BlockItem::Declaration(dec) => declaration_to_c(dec),
    BlockItem::Statement(stmt)  => statement_to_c(stmt),
  }
}

fn declaration_specifiers_to_c(specs: &Vec<DeclarationSpecifier>) -> String {
  specs.iter()
    .map(declaration_specifier_to_c)
    .collect::<Vec<String>>()
    .join(" ")
}

fn declaration_specifier_to_c(spec: &DeclarationSpecifier) -> String {
  match spec {
    DeclarationSpecifier::StorageClass(scs) => storage_class_specifier_to_c(scs),
    DeclarationSpecifier::TypeSpecifier(ty) => type_to_c(ty),
  }
}

fn type_to_c(ty: &Type) -> String {
  match ty {
    Type::Bool   => "bool".to_string(),
    Type::Double => "double".to_string(),
    Type::Float  => "float".to_string(),
    Type::Int    => "int".to_string(),
    Type::Void   => "void".to_string(),
  }
}

fn storage_class_specifier_to_c(scs: &StorageClassSpecifier) -> String {
  match scs {
    StorageClassSpecifier::Extern => "extern".to_string(),
  }
}

fn init_declarators_to_c(decs: &Vec<InitDeclarator>) -> String {
  decs.iter()
    .map(init_declarator_to_c)
    .collect::<Vec<String>>()
    .join(" ")
}

fn init_declarator_to_c(dec: &InitDeclarator) -> String {
  match &dec.expression {
    None => declarator_to_c(&dec.declarator),
    Some(expr) => format!("{} = {}",
                          declarator_to_c(&dec.declarator),
                          expression_to_c(&expr)),
  }
}

fn declarator_to_c(dec: &Declarator) -> String {
  match dec {
    Declarator::Identifier{name} => name.clone()
  }
}

fn declaration_to_c(dec: &Declaration) -> String {
  let specs_c = declaration_specifiers_to_c(&dec.specifiers);
  let decs_c = init_declarators_to_c(&dec.declarators);
  format!("{} {}", specs_c, decs_c)
}
