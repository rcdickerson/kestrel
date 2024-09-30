#[derive(Clone, Debug, PartialEq)]
pub enum CRel {
  Declaration(Declaration),
  FunctionDefinition {
    specifiers: Vec<DeclarationSpecifier>,
    name: String,
    params: Vec<ParameterDeclaration>,
    body: Box<Statement>,
  },
  Seq(Vec<CRel>),
}

/* Declarations */

#[derive(Clone, Debug, PartialEq)]
pub enum Declarator {
  Identifier{name: String},
  Array{name: String, sizes: Vec<Expression>},
  Function{name: String, params: Vec<ParameterDeclaration>},
  Pointer(Box<Declarator>),
}

impl Declarator {
  pub fn expect_function(&self) -> (&String, &Vec<ParameterDeclaration>) {
    match self {
      Declarator::Function{name, params} => (name, params),
      _ => panic!("Expected function declarator, got: {:?}", self),
    }
  }

  pub fn name(&self) -> String {
    match &self {
      Declarator::Identifier{name} => name.clone(),
      Declarator::Array{name, ..} => name.clone(),
      Declarator::Function{name, ..} => name.clone(),
      Declarator::Pointer(inner) => inner.name(),
    }
  }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Declaration {
  pub specifiers: Vec<DeclarationSpecifier>,
  pub declarator: Declarator,
  pub initializer: Option<Expression>
}
impl Declaration {
  pub fn get_type(&self) -> Option<Type> {
    for spec in &self.specifiers {
      match spec {
        DeclarationSpecifier::TypeSpecifier(ty) => {
          return Some(ty.clone());
        },
        _ => { continue; },
      }
    }
    None
  }
}

#[derive(Clone, Debug, PartialEq)]
pub struct ParameterDeclaration {
  pub specifiers: Vec<DeclarationSpecifier>,
  pub declarator: Option<Declarator>,
}
impl ParameterDeclaration {
  pub fn get_type(&self) -> Option<Type> {
    for spec in &self.specifiers {
      match spec {
        DeclarationSpecifier::TypeSpecifier(ty) => {
          return Some(ty.clone());
        },
        _ => { continue; },
      }
    }
    None
  }

  pub fn as_declaration(&self) -> Option<Declaration> {
    self.declarator.as_ref()?;
    Some(Declaration {
      specifiers: self.specifiers.clone(),
      declarator: self.declarator.as_ref().unwrap().clone(),
      initializer: None,
    })
  }
}

#[derive(Clone, Debug, PartialEq)]
pub enum DeclarationSpecifier {
  StorageClass(StorageClassSpecifier),
  TypeSpecifier(Type),
  TypeQualifier(TypeQualifier),
}

#[derive(Clone, Debug, PartialEq)]
pub enum Type {
  Bool,
  Double,
  Float,
  Int,
  Void,
}

#[derive(Clone, Debug, PartialEq)]
pub enum TypeQualifier {
  Const,
}

#[derive(Clone, Debug, PartialEq)]
pub enum StorageClassSpecifier {
  Extern,
}


/* Expressions */

#[derive(Clone, Debug, PartialEq)]
pub enum Expression {
  Identifier{ name: String },
  ConstInt(i32),
  ConstFloat(f32),
  StringLiteral(String),
  Call {
    callee: Box<Expression>,
    args: Vec<Expression>,
  },
  Unop {
    expr: Box<Expression>,
    op: UnaryOp,
  },
  Binop {
    lhs: Box<Expression>,
    rhs: Box<Expression>,
    op: BinaryOp,
  },
  Forall {
    bindings: Vec<(String, Type)>,
    condition: Box<Expression>,
  },
  Statement(Box<Statement>),
}

impl Expression {
  pub fn is_none(&self) -> bool {
    match self {
      Expression::Statement(stmt) => stmt.is_none(),
      _ => false,
    }
  }
}


#[derive(Clone, Debug, PartialEq)]
pub enum UnaryOp {
  Minus,
  Not,
}

#[derive(Clone, Debug, PartialEq)]
pub enum BinaryOp {
  Add,
  And,
  Assign,
  Sub,
  Div,
  Equals,
  Gt,
  Gte,
  Index,
  Lt,
  Lte,
  Mod,
  Mul,
  NotEquals,
  Or,
}


/* Statements */

#[derive(Clone, Debug, PartialEq)]
pub enum Statement {
  BasicBlock(Vec<BlockItem>),
  Break,
  Compound(Vec<BlockItem>),
  Expression(Box<Expression>),
  If {
    condition: Box<Expression>,
    then: Box<Statement>,
    els: Option<Box<Statement>>,
  },
  None,
  Relation {
    lhs: Box<Statement>,
    rhs: Box<Statement>,
  },
  Return(Option<Box<Expression>>),
  While {
    loop_id: Option<String>,
    invariants: Vec<Expression>,
    condition: Box<Expression>,
    body: Option<Box<Statement>>,
    is_runoff: bool,
  },
}

impl Statement {
  pub fn is_none(&self) -> bool {
    match self {
      Statement::None => true,
      Statement::Expression(expr) => expr.is_none(),
      _ => false,
    }
  }
}

#[derive(Clone, Debug, PartialEq)]
pub enum BlockItem {
  Declaration(Declaration),
  Statement(Statement),
}
