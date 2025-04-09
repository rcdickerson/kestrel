use crate::crel::ast::*;
use crate::syrtos as Daf;
use std::collections::HashMap;

impl CRel {
  pub fn to_dafny(&self) -> (String, HashMap<String, (usize, usize)>) {
    let mut source = Daf::Source::new();
    crel_to_daf(self, &mut source);
    source.disable_termination_checking().write()
  }
}

impl ParameterDeclaration {
  pub fn to_dafny(&self) -> Daf::Parameter {
    param_decl_to_param(self)
  }
}

fn crel_to_daf(crel: &CRel, source: &mut Daf::Source) {
  match crel {
    CRel::Declaration(decl) => {
      let mut builder = DeclarationBuilder::new();
      builder.visit_init_declarator(decl);
      builder.build(source);
    },
    CRel::FunctionDefinition{specifiers, name, params, body} => {
      source.push_method(&fun_to_daf(specifiers, name, params, body));
    },
    CRel::Seq(seq) => {
      for crel in seq { crel_to_daf(crel, source) }
    }
  };
}

fn fun_to_daf(specifiers: &Vec<DeclarationSpecifier>,
              name: &String,
              params: &Vec<ParameterDeclaration>,
              body: &Statement) -> Daf::Method {
  let mut ret_type = None;
  for spec in specifiers {
    match spec {
      DeclarationSpecifier::TypeSpecifier(ts) => {
        ret_type = type_to_daf(ts);
      }
      _ => (),
    }
  }

  let mut method = Daf::Method::new(name, ret_type);
  for param in params.iter()
    .filter(|param| param.declarator.is_some())
    .map(decl_to_param) {
      method.push_param(&param);
    }
  method.set_body(&statement_to_daf(body));
  method
}

fn decl_to_param(decl: &ParameterDeclaration) -> Daf::Parameter {
  let mut builder = DeclarationBuilder::new();
  for spec in &decl.specifiers {
    builder.visit_specifier(spec);
  }
  if let Some(decl) = decl.declarator.as_ref() { builder.visit_declarator(decl) }
  builder.build_param()
}

fn param_decl_to_param(decl: &ParameterDeclaration) -> Daf::Parameter {
  let mut builder = DeclarationBuilder::new();
  for spec in &decl.specifiers {
    builder.visit_specifier(spec);
  }
  if decl.declarator.as_ref().is_some() {
    builder.visit_declarator(decl.declarator.as_ref().unwrap());
  }
  builder.build_param()
}

fn expression_to_daf(expr: &Expression) -> Daf::Expression {
  match expr {
    Expression::Identifier{name} => Daf::Expression::Identifier {
      name: name.clone(),
    },
    Expression::ConstBool(true) => Daf::Expression::ConstTrue,
    Expression::ConstBool(false) => Daf::Expression::ConstFalse,
    Expression::ConstInt(i) => Daf::Expression::ConstInt(*i),
    Expression::ConstFloat(f) => Daf::Expression::ConstFloat(*f),
    Expression::StringLiteral(s) => Daf::Expression::StringLiteral(s.clone()),
    Expression::Call{ callee, args } => {
      Daf::Expression::FnCall {
        name: Box::new(expression_to_daf(callee)),
        args: args.iter()
          .map(expression_to_daf)
          .collect::<Vec<Daf::Expression>>(),
      }
    },
    Expression::ASpecCall{ callee, args } => {
      Daf::Expression::FnCall {
        name: Box::new(expression_to_daf(callee)),
        args: args.iter()
          .map(expression_to_daf)
          .collect::<Vec<Daf::Expression>>(),
      }
    },
    Expression::ESpecCall{ callee, args } => {
      Daf::Expression::FnCall {
        name: Box::new(expression_to_daf(callee)),
        args: args.iter()
          .map(expression_to_daf)
          .collect::<Vec<Daf::Expression>>(),
      }
    },
    Expression::Unop{ expr, op } => {
      let expr = Box::new(expression_to_daf(expr));
      let op = match op {
        UnaryOp::Minus => "-".to_string(),
        UnaryOp::Not   => "!".to_string(),
      };
      Daf::Expression::UnOp{expr, op}
    },
    Expression::Binop{ lhs, rhs, op } => {
      let lhs = Box::new(expression_to_daf(lhs));
      let rhs = Box::new(expression_to_daf(rhs));
      match op {
        BinaryOp::Add       => Daf::Expression::BinOp{lhs, rhs, op: "+".to_string()},
        BinaryOp::And       => Daf::Expression::BinOp{lhs, rhs, op: "&&".to_string()},
        BinaryOp::Assign    => Daf::Expression::BinOp{lhs, rhs, op: ":=".to_string()},
        BinaryOp::Sub       => Daf::Expression::BinOp{lhs, rhs, op: "-".to_string()},
        BinaryOp::Div       => Daf::Expression::BinOp{lhs, rhs, op: "/".to_string()},
        BinaryOp::Equals    => Daf::Expression::BinOp{lhs, rhs, op: "==".to_string()},
        BinaryOp::Gt        => Daf::Expression::BinOp{lhs, rhs, op: ">".to_string()},
        BinaryOp::Gte       => Daf::Expression::BinOp{lhs, rhs, op: ">=".to_string()},
        BinaryOp::Index     => Daf::Expression::ArrayIndex{expr: lhs, index: rhs},
        BinaryOp::Lt        => Daf::Expression::BinOp{lhs, rhs, op: "<".to_string()},
        BinaryOp::Lte       => Daf::Expression::BinOp{lhs, rhs, op: "<=".to_string()},
        BinaryOp::Mod       => Daf::Expression::BinOp{lhs, rhs, op: "%".to_string()},
        BinaryOp::Mul       => Daf::Expression::BinOp{lhs, rhs, op: "*".to_string()},
        BinaryOp::NotEquals => Daf::Expression::BinOp{lhs, rhs, op: "!=".to_string()},
        BinaryOp::Or        => Daf::Expression::BinOp{lhs, rhs, op: "||".to_string()},
      }
    },
    Expression::Forall { bindings, condition } => {
      Daf::Expression::Forall {
        bindings: bindings.iter().map(|(v, t)| (v.clone(), type_to_daf(t).unwrap())).collect(),
        condition: Box::new(expression_to_daf(condition))
      }
    }
    Expression::Statement(stmt) => match statement_to_daf(stmt) {
      Daf::Statement::Expression(expr) => *expr,
      daf_stmt => Daf::Expression::Statement(Box::new(daf_stmt))
    },
  }
}

fn statement_to_daf(stmt: &Statement) -> Daf::Statement {
  match stmt {
    Statement::Assert(expr) => {
      let daf_expr = match expression_to_daf(expr) {
        Daf::Expression::ConstInt(0) => Daf::Expression::ConstFalse,
        Daf::Expression::ConstInt(_) => Daf::Expression::ConstTrue,
        expr => expr,
      };
      Daf::Statement::Assert(Box::new(daf_expr))
    },
    Statement::Assume(expr) => {
      let daf_expr = match expression_to_daf(expr) {
        Daf::Expression::ConstInt(0) => Daf::Expression::ConstFalse,
        Daf::Expression::ConstInt(_) => Daf::Expression::ConstTrue,
        expr => expr,
      };
      Daf::Statement::Assume(Box::new(daf_expr))
    },
    Statement::BasicBlock(items) => {
      Daf::Statement::Seq(items.iter().map(block_item_to_daf).collect())
    },
    Statement::Break => Daf::Statement::Break,
    Statement::Compound(items) => {
      Daf::Statement::Seq(items.iter().map(block_item_to_daf).collect())
    },
    Statement::Expression(expr) => match expression_to_daf(expr) {
      Daf::Expression::Statement(stmt) => *stmt,
      daf_expr => Daf::Statement::Expression(Box::new(daf_expr))
    },
    Statement::GuardedRepeat{repetitions, condition, body, ..} => {
      let mut ifs = Vec::new();
      for _ in 0..*repetitions {
        ifs.push(Daf::Statement::If {
          condition: Box::new(expression_to_daf(condition)),
          then: Box::new(statement_to_daf(body)),
          els: None,
        });
      }
      Daf::Statement::Seq(ifs)
    },
    Statement::If{condition, then, els} => {
      Daf::Statement::If {
        condition: Box::new(expression_to_daf(condition)),
        then: Box::new(statement_to_daf(then)),
        els: els.as_ref().map(|stmt| Box::new(statement_to_daf(stmt)))
      }
    },
    Statement::None => Daf::Statement::Seq(Vec::new()),
    Statement::Relation{ lhs, rhs } => {
      Daf::Statement::Seq(vec!(statement_to_daf(lhs), statement_to_daf(rhs)))
    }
    Statement::Return(expr) => match expr {
      None => { Daf::Statement::Return(None) },
      Some(ret) => { Daf::Statement::Return(Some(Box::new(expression_to_daf(ret)))) },
    },
    Statement::While{id, invariants, condition, body, ..} => {
      let condition = Box::new(expression_to_daf(condition));
      let invariants = invariants.iter().map(|invar| expression_to_daf(invar)).collect();
      let body = body.as_ref().map(|stmt| Box::new(statement_to_daf(stmt)));
      Daf::Statement::While{loop_id: Some(loop_head_name(id)), invariants, condition, body}
    },
  }
}

fn block_item_to_daf(item: &BlockItem) -> Daf::Statement {
  match item {
    BlockItem::Declaration(decl) => {
      let mut builder = DeclarationBuilder::new();
      builder.visit_init_declarator(decl);
      Daf::Statement::Variable(builder.build_variable())
    },
    BlockItem::Statement(stmt) => statement_to_daf(stmt),
  }
}

fn type_to_daf(ty: &Type) -> Option<Daf::Type> {
  match ty {
    Type::Bool   => Some(Daf::Type::Bool),
    Type::Double => Some(Daf::Type::Real),
    Type::Float  => Some(Daf::Type::Real),
    Type::Int    => Some(Daf::Type::Int),
    Type::Void   => None,
  }
}

/// Auxilliary builder to help construct variables and parameters.
struct DeclarationBuilder {
  name: Option<String>,
  ty: Option<Daf::Type>,
  val: Option<Daf::Expression>,
  is_array: bool,
  array_sizes: Vec<Daf::Expression>,
  is_function: bool,
  function_params: Option<Vec<Daf::Parameter>>,
  is_const: bool,
}

impl DeclarationBuilder {

  fn new() -> Self {
    DeclarationBuilder {
      name: None,
      ty: None,
      val: None,
      is_array: false,
      array_sizes: Vec::new(),
      is_function: false,
      function_params: None,
      is_const: false,
    }
  }

  fn visit_specifier(&mut self, spec: &DeclarationSpecifier) {
    match spec {
      DeclarationSpecifier::StorageClass(sc_spec) => {
        match sc_spec {
          StorageClassSpecifier::Extern => (), // TODO
        }
      }
      DeclarationSpecifier::TypeSpecifier(ts) => {
        self.ty = type_to_daf(ts);
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
        self.val = Some(expression_to_daf(expr));
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
        self.array_sizes = sizes.iter().map(expression_to_daf).collect();
      },
      Declarator::Function{name, params} => {
        self.name = Some(name.clone());
        self.is_function = true;
        self.function_params = Some(params.iter().map(param_decl_to_param).collect())
      },
      Declarator::Pointer(decl) => {
        // TODO: No pointers in Dafny
        self.visit_declarator(decl);
      }
    }
  }

  fn build(&self, source: &mut Daf::Source) {
    if self.is_function {
      source.push_function(&self.build_function());
    } else {
      source.declare_variable(&self.build_variable());
    }
  }

  fn build_function(&self) -> Daf::Function {
    let mut fun = Daf::Function::new(
      self.name.clone().expect("Variable declaration has no name").as_str(),
      self.ty.clone().expect("Variable declaration has no type"));
    if let Some(params) = &self.function_params {
      for param in params { fun.push_param(&param); }
    }
    fun
  }

  fn build_variable(&self) -> Daf::Variable {
    let mut var = Daf::Variable::new(
      self.ty.clone().expect("Variable declaration has no type"),
      self.name.clone().expect("Variable declaration has no name")
    );
    self.val.as_ref().map(|expr| var.set_value(expr));
    var.set_const(self.is_const);
    var
  }

  fn build_param(&self) -> Daf::Parameter {
    if self.is_function { panic!("Unsupported: function declarator as function parameter"); }
    if self.val.is_some() { panic!("Unsupported: function parameter initialized to value"); }

    let ty = self.ty.as_ref().expect("Parameter has no type").clone();
    let mut param = match self.name.as_ref() {
      None => Daf::Parameter::anonymous(ty),
      Some(name) => Daf::Parameter::new(name, ty),
    };
    param.set_array(self.is_array);
    param.set_array_sizes(&self.array_sizes);
    param
  }
}
