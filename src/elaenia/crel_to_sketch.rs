use crate::crel::ast::*;
use crate::escher as Sk;

impl CRel {
  pub fn to_sketch(&self) -> String {
    let mut source = Sk::Source::new();
    crel_to_sketch(self, &mut source);
    source.to_string()
  }
}

impl ParameterDeclaration {
  pub fn to_sketch(&self) -> Sk::FunctionParameter {
    param_decl_to_param(self)
  }
}

fn crel_to_sketch(crel: &CRel, source: &mut Sk::Source) {
  match crel {
    CRel::Declaration(decl) => {
      source.declare_variable(&declaration_to_sketch(decl));
    },
    CRel::FunctionDefinition{specifiers, name, params, body} => {
      source.push_function(&fun_to_sketch(specifiers, name, params, body));
    },
    CRel::Seq(seq) => {
      for crel in seq { crel_to_sketch(crel, source) }
    }
  }
}

pub fn declaration_to_sketch(decl: &Declaration) -> Sk::Variable {
  let mut builder = DeclarationBuilder::new();
  builder.visit_init_declarator(decl);
  builder.build_variable()
}

pub fn fun_to_sketch(specifiers: &Vec<DeclarationSpecifier>,
                     name: &String,
                     params: &Vec<ParameterDeclaration>,
                     body: &Statement) -> Sk::Function {
  let mut fun_ty = Sk::Type::Void;
  for spec in specifiers {
    match spec {
      DeclarationSpecifier::TypeSpecifier(ts) => {
        fun_ty = type_to_sketch(ts);
      },
      DeclarationSpecifier::StorageClass(sc_spec) => {
        match sc_spec {
          StorageClassSpecifier::Extern => {
            println!("Warning, extern unsupported in Sketch, dropping. For function: {}", name);
          },
        }
      },
      DeclarationSpecifier::TypeQualifier(tq) => {
        match tq {
          TypeQualifier::Const => {
            println!("Warning, const unsupported in Sketch functions, dropping. For function: {}", name);
          }
        }
      },
    }
  }

  let mut fun = Sk::Function::new(name, fun_ty);
  for param in params.iter()
    .filter(|param| param.declarator.is_some())
    .map(decl_to_param) {
      fun.push_param(&param);
    }
  fun.set_body(&statement_to_sketch(body));
  fun
}

fn decl_to_param(decl: &ParameterDeclaration) -> Sk::FunctionParameter {
  let mut builder = DeclarationBuilder::new();
  for spec in &decl.specifiers {
    builder.visit_specifier(spec);
  }
  if let Some(decl) = decl.declarator.as_ref() { builder.visit_declarator(decl) }
  builder.build_param()
}

fn param_decl_to_param(decl: &ParameterDeclaration) -> Sk::FunctionParameter {
  let mut builder = DeclarationBuilder::new();
  for spec in &decl.specifiers {
    builder.visit_specifier(spec);
  }
  if decl.declarator.as_ref().is_some() {
    builder.visit_declarator(decl.declarator.as_ref().unwrap());
  }
  builder.build_param()
}

fn expression_to_sketch(expr: &Expression) -> Sk::Expression {
  match expr {
    Expression::Identifier{name} => Sk::Expression::Identifier {
      name: name.clone(),
    },
    Expression::ConstBool(b) => Sk::Expression::ConstInt(if *b { 1 } else { 0 }),
    Expression::ConstInt(i) => Sk::Expression::ConstInt(*i),
    Expression::ConstFloat(f) => Sk::Expression::ConstFloat(*f),
    Expression::StringLiteral(s) => Sk::Expression::StringLiteral(s.clone()),
    Expression::Call{ callee, args } => {
      Sk::Expression::FnCall {
        name: Box::new(expression_to_sketch(callee)),
        args: args.iter()
          .map(expression_to_sketch)
          .collect::<Vec<Sk::Expression>>(),
      }
    },
    Expression::Unop{ expr, op } => {
      let expr = Box::new(expression_to_sketch(expr));
      let op = match op {
        UnaryOp::Minus => "-".to_string(),
        UnaryOp::Not   => "!".to_string(),
      };
      Sk::Expression::UnOp{expr, op}
    },
    Expression::Binop{ lhs, rhs, op } => {
      let lhs = Box::new(expression_to_sketch(lhs));
      let rhs = Box::new(expression_to_sketch(rhs));
      match op {
        BinaryOp::Add       => Sk::Expression::BinOp{lhs, rhs, op: "+".to_string()},
        BinaryOp::And       => Sk::Expression::BinOp{lhs, rhs, op: "&&".to_string()},
        BinaryOp::Assign    => Sk::Expression::BinOp{lhs, rhs, op: "=".to_string()},
        BinaryOp::Sub       => Sk::Expression::BinOp{lhs, rhs, op: "-".to_string()},
        BinaryOp::Div       => Sk::Expression::BinOp{lhs, rhs, op: "/".to_string()},
        BinaryOp::Equals    => Sk::Expression::BinOp{lhs, rhs, op: "==".to_string()},
        BinaryOp::Gt        => Sk::Expression::BinOp{lhs, rhs, op: ">".to_string()},
        BinaryOp::Gte       => Sk::Expression::BinOp{lhs, rhs, op: ">=".to_string()},
        BinaryOp::Index     => Sk::Expression::ArrayIndex{expr: lhs, index: rhs},
        BinaryOp::Lt        => Sk::Expression::BinOp{lhs, rhs, op: "<".to_string()},
        BinaryOp::Lte       => Sk::Expression::BinOp{lhs, rhs, op: "<=".to_string()},
        BinaryOp::Mod       => Sk::Expression::BinOp{lhs, rhs, op: "%".to_string()},
        BinaryOp::Mul       => Sk::Expression::BinOp{lhs, rhs, op: "*".to_string()},
        BinaryOp::NotEquals => Sk::Expression::BinOp{lhs, rhs, op: "!=".to_string()},
        BinaryOp::Or        => Sk::Expression::BinOp{lhs, rhs, op: "||".to_string()},
      }
    },
    Expression::Forall{..} => {
      println!("WARNING: Foralls are unsupported! Treating as true.");
      Sk::Expression::ConstInt(1)
    },
    Expression::SketchHole => Sk::Expression::Hole,
    Expression::Ternary{ condition, then, els } => Sk::Expression::Ternary {
      condition: Box::new(expression_to_sketch(condition)),
      then: Box::new(expression_to_sketch(then)),
      els: Box::new(expression_to_sketch(els)),
    },
    Expression::Statement(stmt) => match statement_to_sketch(stmt) {
      Sk::Statement::Expression(expr) => *expr,
      c_stmt => Sk::Expression::Statement(Box::new(c_stmt)),
    },
  }
}

fn initializer_to_sketch(initializer: &Initializer) -> Option<Sk::Initializer> {
  fn is_singleton_zero(inits: &Vec<Initializer>) -> bool {
    if inits.len() != 1 { return false }
    match inits.get(0).unwrap() {
      &Initializer::Expression(Expression::ConstInt(0)) => true,
      _ => false,
    }
  }

  match initializer {
    Initializer::Expression(expr) => {
      Some(Sk::Initializer::Expression(expression_to_sketch(expr)))
    },
    Initializer::List(inits) if is_singleton_zero(inits) => {
      None
    },
    Initializer::List(inits) => {
      Some(Sk::Initializer::List(inits.into_iter()
          .map(initializer_to_sketch)
          .map(|init| init.unwrap_or(
            Sk::Initializer::Expression(Sk::Expression::ConstInt(0))))
          .collect()))
    },
  }
}
/*
fn handle_forall(condition: &Expression,
                 bindings: &Vec<(String, Type)>)
                 -> Sk::Statement {
  let mut bound_cond = condition.clone();
  let mut forall_functions = Vec::new();
  let mut forall_vars = Vec::new();
  let mut var_id = 0;
  for (name, ty) in bindings {
    let sketch_type = type_to_sketch(ty);
    let var_name = format!("_{}_{}", name, var_id);
    let fun_name = format!("_forall_{}", var_name);
    let mut var = Sk::Variable::new(sketch_type.clone());
    var.set_name(var_name.clone());
    var.set_initializer(Sk::Initializer::Expression(
      Sk::Expression::FnCall {
        name: Box::new(Sk::Expression::Identifier{name: fun_name.clone()}),
        args: Vec::new(),
      }
    ));
    forall_functions.push(Sk::Function::new(&fun_name, sketch_type));
    forall_vars.push(Sk::Statement::Variable(var));
    bound_cond = bound_cond.map_vars(&|v| {
      if v == *name { var_name.clone() } else { v }
    });
    var_id += 1;
  }
  Sk::Statement::Seq(vec!())
}
*/

fn break_ands(expr: &Expression) -> Vec<Expression> {
  match expr {
    Expression::Binop{lhs, rhs, op} if *op == BinaryOp::And => {
      let mut exprs = vec!(*lhs.clone());
      exprs.append(&mut break_ands(rhs));
      exprs
    },
    _ => vec!(expr.clone()),
  }
}

fn statement_to_sketch(stmt: &Statement) -> Sk::Statement {
  match stmt {
    Statement::Assert(expr) => {
      let asserts = break_ands(expr).into_iter()
        .map(|expr| Sk::Statement::Assert(Box::new(expression_to_sketch(&expr))))
        .collect::<Vec<_>>();
      if asserts.len() == 1 {
        asserts.get(0).unwrap().clone()
      } else {
        Sk::Statement::Seq(asserts)
      }
    },
    Statement::Assume(expr) => {
      let assumes = break_ands(expr).into_iter()
        .map(|expr| Sk::Statement::Assume(Box::new(expression_to_sketch(&expr))))
        .collect::<Vec<_>>();
      if assumes.len() == 1 {
        assumes.get(0).unwrap().clone()
      } else {
        Sk::Statement::Seq(assumes)
      }
    },
    Statement::BasicBlock(items) => {
      Sk::Statement::Seq(items.iter().map(block_item_to_sketch).collect())
    },
    Statement::Break => Sk::Statement::Break,
    Statement::Compound(items) => {
      Sk::Statement::Seq(items.iter().map(block_item_to_sketch).collect())
    },
    Statement::Expression(expr) => match expression_to_sketch(expr) {
      Sk::Expression::Statement(stmt) => *stmt,
      c_expr => Sk::Statement::Expression(Box::new(c_expr)),
    },
    Statement::GuardedRepeat{repetitions, condition, body, ..} => {
      let mut ifs = Vec::new();
      for _ in 0..*repetitions {
        ifs.push(Sk::Statement::If {
          condition: Box::new(expression_to_sketch(condition)),
          then: Box::new(statement_to_sketch(body)),
          els: None,
        });
      }
      Sk::Statement::Seq(ifs)
    },
    Statement::If{condition, then, els} => {
      Sk::Statement::If {
        condition: Box::new(expression_to_sketch(condition)),
        then: Box::new(statement_to_sketch(then)),
        els: els.as_ref().map(|stmt| Box::new(statement_to_sketch(stmt)))
      }
    },
    Statement::None => Sk::Statement::Seq(Vec::new()),
    Statement::Relation{ lhs, rhs } => {
      Sk::Statement::Seq(vec!(statement_to_sketch(lhs), statement_to_sketch(rhs)))
    }
    Statement::Return(expr) => match expr {
      None => { Sk::Statement::Return(None) },
      Some(ret) => { Sk::Statement::Return(Some(Box::new(expression_to_sketch(ret)))) },
    },
    Statement::While{is_runoff, condition, ..} if *is_runoff => {
      Sk::Statement::Assert(Box::new(Sk::Expression::UnOp {
        expr: Box::new(expression_to_sketch(condition)),
        op: "!".to_string(),
      }))
    },
    Statement::While{id, condition, body, ..} => {
      let counter_name = format!("_{}", id).replace("-", "");
      let counter_ident = Sk::Expression::Identifier{name: counter_name.clone()};
      let mut counter_var = Sk::Variable::new(Sk::Type::Int);
      counter_var.set_name(counter_name.clone());
      counter_var.set_initializer(Sk::Initializer::Expression(Sk::Expression::ConstInt(0)));
      let counter_decl = Sk::Statement::Variable(counter_var);

      let counter_check = Sk::Statement::Seq(vec!(
        Sk::Statement::If {
          condition: Box::new(Sk::Expression::BinOp {
            lhs: Box::new(counter_ident.clone()),
            rhs: Box::new(Sk::Expression::ConstInt(5)),
            op: ">".to_string(),
          }),
          then: Box::new(Sk::Statement::Assume(
            Box::new(Sk::Expression::ConstBool(false)))),
          els: None,
        },
      ));
      let counter_inc = Sk::Statement::Expression(Box::new(
        Sk::Expression::BinOp {
          lhs: Box::new(counter_ident.clone()),
          rhs: Box::new(Sk::Expression::BinOp {
            lhs: Box::new(counter_ident.clone()),
            rhs: Box::new(Sk::Expression::ConstInt(1)),
            op: "+".to_string(),
          }),
          op: "=".to_string(),
        }
      ));

      let condition = Box::new(expression_to_sketch(condition));
      let body = match &body {
        None => Sk::Statement::Seq(vec!(counter_check, counter_inc)),
        Some(stmt) => Sk::Statement::Seq(vec!(
          statement_to_sketch(stmt),
          counter_check,
          counter_inc)),
      };
      Sk::Statement::Seq(vec!(
        counter_decl,
        Sk::Statement::While{condition, body: Some(Box::new(body))}))
    },
  }
}

fn block_item_to_sketch(item: &BlockItem) -> Sk::Statement {
  match item {
    BlockItem::Declaration(decl) => {
      Sk::Statement::Variable(declaration_to_sketch(decl))
    },
    BlockItem::Statement(stmt) => statement_to_sketch(stmt),
  }
}

fn type_to_sketch(ty: &Type) -> Sk::Type {
  match ty {
    Type::Bool   => Sk::Type::Bit,
    Type::Double => Sk::Type::Double,
    Type::Float  => Sk::Type::Float,
    Type::Int    => Sk::Type::Int,
    Type::Void   => Sk::Type::Void,
  }
}


/// Auxilliary builder to help construct variables and parameters.
struct DeclarationBuilder {
  name: Option<String>,
  ty: Option<Sk::Type>,
  init: Option<Sk::Initializer>,
  is_array: bool,
  array_sizes: Vec<Sk::Expression>,
  is_extern: bool,
  is_function: bool,
  function_params: Option<Vec<Sk::FunctionParameter>>,
  is_const: bool,
  is_pointer: bool,
}

impl DeclarationBuilder {

  fn new() -> Self {
    DeclarationBuilder {
      name: None,
      ty: None,
      init: None,
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
        self.ty = Some(type_to_sketch(ts));
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
    self.init = match decl.initializer.as_ref() {
      None => None,
      Some(init) => initializer_to_sketch(&init),
    };
  }

  fn visit_declarator(&mut self, decl: &Declarator) {
    match &decl {
      Declarator::Identifier{name} => {
        self.name = Some(name.clone());
      },
      Declarator::Array{name, sizes} => {
        self.name = Some(name.clone());
        self.is_array = true;
        self.array_sizes = sizes.iter().map(expression_to_sketch).collect();
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

  fn build_variable(&self) -> Sk::Variable {
    let mut var = Sk::Variable::new(
      self.ty.clone().expect("Variable declaration has no type"));
    self.name.as_ref().map(|name| var.set_name(name.clone()));
    var.set_const(self.is_const);
    var.set_array(self.is_array);
    var.set_array_sizes(&self.array_sizes);
    var.set_function(self.is_function);
    self.function_params.as_ref().map(|params| var.set_function_params(params.clone()));
    self.init.as_ref().map(|init| var.set_initializer(init.clone()));
    var.set_pointer(self.is_pointer);
    var
  }

  fn build_param(&self) -> Sk::FunctionParameter {
    if self.is_function { panic!("Unsupported: function declarator as function parameter"); }
    if self.is_extern { panic!("Unsupported: extern function parameter"); }
    if self.init.is_some() { panic!("Unsupported: function parameter initialized to value"); }

    let ty = self.ty.as_ref().expect("Parameter has no type").clone();
    let mut param = match self.name.as_ref() {
      None => Sk::FunctionParameter::anonymous(ty),
      Some(name) =>  Sk::FunctionParameter::new(name, ty),
    };
    param.set_array(self.is_array);
    param.set_const(self.is_const);
    param.set_pointer(self.is_pointer);
    param.set_array_sizes(&self.array_sizes);
    param
  }
}
