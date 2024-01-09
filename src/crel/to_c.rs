use crate::crel::ast::*;
use crate::shanty as C;

impl CRel {
  pub fn to_c(&self) -> String {
    let mut source = C::Source::new();
    crel_to_c(self, &mut source);
    source.to_string()
  }
}

impl ParameterDeclaration {
  pub fn to_c(&self) -> C::FunctionParameter {
    param_decl_to_param(self)
  }
}

fn crel_to_c(crel: &CRel, source: &mut C::Source) {
  match crel {
    CRel::Declaration(decl) => {
      source.declare_variable(&declaration_to_c(decl));
    },
    CRel::FunctionDefinition{specifiers, name, params, body} => {
      source.push_function(&fun_to_c(specifiers, name, params, body));
    },
    CRel::Seq(seq) => {
      for crel in seq { crel_to_c(crel, source) }
    }
  }
}

fn declaration_to_c(decl: &Declaration) -> C::Variable {
  let mut builder = DeclarationBuilder::new();
  builder.visit_init_declarator(decl);
  builder.build_variable()
}

fn fun_to_c(specifiers: &Vec<DeclarationSpecifier>,
            name: &String,
            params: &Vec<ParameterDeclaration>,
            body: &Statement) -> C::Function {
  let mut fun_ty = C::Type::Void;
  let mut fun_extern = false;
  let mut fun_const = false;
  for spec in specifiers {
    match spec {
      DeclarationSpecifier::StorageClass(sc_spec) => {
        match sc_spec {
          StorageClassSpecifier::Extern => fun_extern = true,
        }
      }
      DeclarationSpecifier::TypeSpecifier(ts) => {
        fun_ty = type_to_c(ts);
      }
      DeclarationSpecifier::TypeQualifier(tq) => {
        match tq {
          TypeQualifier::Const => fun_const = true,
        }
      }
    }
  }

  let mut fun = C::Function::new(name, fun_ty);
  for param in params.iter()
    .filter(|param| param.declarator.is_some())
    .map(decl_to_param) {
      fun.push_param(&param);
    }
  fun.set_extern(fun_extern);
  fun.set_const(fun_const);
  fun.set_body(&statement_to_c(body));
  fun
}

fn decl_to_param(decl: &ParameterDeclaration) -> C::FunctionParameter {
  let mut builder = DeclarationBuilder::new();
  for spec in &decl.specifiers {
    builder.visit_specifier(spec);
  }
  if let Some(decl) = decl.declarator.as_ref() { builder.visit_declarator(decl) }
  builder.build_param()
}

fn param_decl_to_param(decl: &ParameterDeclaration) -> C::FunctionParameter {
  let mut builder = DeclarationBuilder::new();
  for spec in &decl.specifiers {
    builder.visit_specifier(spec);
  }
  if decl.declarator.as_ref().is_some() {
    builder.visit_declarator(decl.declarator.as_ref().unwrap());
  }
  builder.build_param()
}

fn expression_to_c(expr: &Expression) -> C::Expression {
  match expr {
    Expression::Identifier{name} => C::Expression::Identifier {
      name: name.clone(),
    },
    Expression::ConstInt(i) => C::Expression::ConstInt(*i),
    Expression::ConstFloat(f) => C::Expression::ConstFloat(*f),
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
        els: els.as_ref().map(|stmt| Box::new(statement_to_c(stmt)))
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
      let body = body.as_ref().map(|stmt| Box::new(statement_to_c(stmt)));
      C::Statement::While{condition, body}
    }
  }
}

fn block_item_to_c(item: &BlockItem) -> C::Statement {
  match item {
    BlockItem::Declaration(decl) => {
      C::Statement::Variable(declaration_to_c(decl))
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


/// Auxilliary builder to help construct variables and parameters.
struct DeclarationBuilder {
  name: Option<String>,
  ty: Option<C::Type>,
  val: Option<C::Expression>,
  is_array: bool,
  array_sizes: Vec<C::Expression>,
  is_extern: bool,
  is_function: bool,
  function_params: Option<Vec<C::FunctionParameter>>,
  is_const: bool,
  is_pointer: bool,
}

impl DeclarationBuilder {

  fn new() -> Self {
    DeclarationBuilder {
      name: None,
      ty: None,
      val: None,
      is_array: false,
      array_sizes: Vec::new(),
      is_extern: false,
      is_function: false,
      function_params: None,
      is_const: false,
      is_pointer: false,
    }
  }

  fn visit_specifier(&mut self, spec: &DeclarationSpecifier) {
    match spec {
      DeclarationSpecifier::StorageClass(sc_spec) => {
        match sc_spec {
          StorageClassSpecifier::Extern => self.is_extern = true,
        }
      }
      DeclarationSpecifier::TypeSpecifier(ts) => {
        self.ty = Some(type_to_c(ts));
      }
      DeclarationSpecifier::TypeQualifier(tq) => {
        match tq {
          TypeQualifier::Const => self.is_const = true,
        }
      }
    }
  }

  fn visit_init_declarator(&mut self, decl: &Declaration) {
    for spec in &decl.specifiers { self.visit_specifier(spec); }
    self.visit_declarator(&decl.declarator);
    match &decl.initializer {
      None => (),
      Some(expr) => {
        self.val = Some(expression_to_c(expr));
      }
    }
  }

  fn visit_declarator(&mut self, decl: &Declarator) {
    match &decl {
      Declarator::Identifier{name} => {
        self.name = Some(name.clone());
      },
      Declarator::Array{name, sizes} => {
        self.name = Some(name.clone());
        self.is_array = true;
        self.array_sizes = sizes.iter().map(expression_to_c).collect();
      },
      Declarator::Function{name, params} => {
        self.name = Some(name.clone());
        self.is_function = true;
        self.function_params = Some(params.iter().map(param_decl_to_param).collect())
      },
      Declarator::Pointer(decl) => {
        self.is_pointer = true;
        self.visit_declarator(decl);
      }
    }
  }

  fn build_variable(&self) -> C::Variable {
    let mut var = C::Variable::new(
      self.ty.clone().expect("Variable declaration has no type"));
    self.name.as_ref().map(|name| var.set_name(name.clone()));
    var.set_extern(self.is_extern);
    var.set_const(self.is_const);
    var.set_array(self.is_array);
    var.set_array_sizes(&self.array_sizes);
    var.set_function(self.is_function);
    self.function_params.as_ref().map(|params| var.set_function_params(params.clone()));
    self.val.as_ref().map(|expr| var.set_value(expr));
    var.set_pointer(self.is_pointer);
    var
  }

  fn build_param(&self) -> C::FunctionParameter {
    if self.is_function { panic!("Unsupported: function declarator as function parameter"); }
    if self.is_extern { panic!("Unsupported: extern function parameter"); }
    if self.val.is_some() { panic!("Unsupported: function parameter initialized to value"); }

    let ty = self.ty.as_ref().expect("Parameter has no type").clone();
    let mut param = match self.name.as_ref() {
      None => C::FunctionParameter::anonymous(ty),
      Some(name) =>  C::FunctionParameter::new(name, ty),
    };
    param.set_array(self.is_array);
    param.set_const(self.is_const);
    param.set_pointer(self.is_pointer);
    param.set_array_sizes(&self.array_sizes);
    param
  }
}
