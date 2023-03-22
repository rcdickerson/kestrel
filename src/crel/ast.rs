#[derive(Clone, Debug)]
pub enum CRel {
  Declaration {
    specifiers: Vec<DeclarationSpecifier>,
    declarators: Vec<InitDeclarator>,
  },
  FunctionDefinition {
    specifiers: Vec<DeclarationSpecifier>,
    name: Declarator,
    params: Vec<Declaration>,
    body: Box<Statement>,
  },
  Seq(Vec<CRel>),
}

#[derive(Clone, Debug)]
pub enum Expression {
  Identifier{ name: String },
  ConstInt(i32),
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

#[derive(Clone, Debug)]
pub enum Statement {
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

#[derive(Clone, Debug)]
pub struct InitDeclarator {
  pub declarator: Declarator,
  pub expression: Option<Expression>
}

#[derive(Clone, Debug)]
pub enum DeclarationSpecifier {
  StorageClass(StorageClassSpecifier),
  TypeSpecifier(Type),
}

#[derive(Clone, Debug)]
pub enum Type {
  Bool,
  Float,
  Int,
  Void,
}

#[derive(Clone, Debug)]
pub enum Declarator {
  Identifier{ name: String },
}

#[derive(Clone, Debug)]
pub struct Declaration {
  pub specifiers: Vec<DeclarationSpecifier>,
  pub declarators: Vec<InitDeclarator>,
}

#[derive(Clone, Debug)]
pub enum UnaryOp {
  Minus,
  Not,
}

#[derive(Clone, Debug)]
pub enum BinaryOp {
  Add,
  And,
  Assign,
  Sub,
  Div,
  Equals,
  Gt,
  Gte,
  Lt,
  Lte,
  Mod,
  Mul,
  Or,
}

#[derive(Clone, Debug)]
pub enum StorageClassSpecifier {
  Extern,
}

#[derive(Clone, Debug)]
pub enum BlockItem {
  Declaration(Declaration),
  Statement(Statement),
}
