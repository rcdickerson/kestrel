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
  Array{name: String, size: Option<Expression>},
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
  Statement(Box<Statement>),
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
    condition: Box<Expression>,
    body: Option<Box<Statement>>,
  },
}

#[derive(Clone, Debug, PartialEq)]
pub enum BlockItem {
  Declaration(Declaration),
  Statement(Statement),
}
