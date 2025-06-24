use std::cmp::Ordering;
use uuid::Uuid;

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
  pub initializer: Option<Initializer>
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
pub enum Initializer {
  Expression(Expression),
  List(Vec<Initializer>),
}

#[derive(Clone, Debug)]
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

impl PartialOrd for ParameterDeclaration {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    match &self.declarator {
      None => match other.declarator {
        None => Some(Ordering::Equal),
        _ => Some(Ordering::Less),
      },
      Some(decl) => match &other.declarator {
        None => Some(Ordering::Greater),
        Some(other_decl) => decl.name().partial_cmp(&other_decl.name()),
      }
    }
  }
}

impl PartialEq for ParameterDeclaration {
  fn eq(&self, other: &ParameterDeclaration) -> bool {
    match &self.declarator {
      None => match other.declarator {
        None => true,
        _ => false,
      },
      Some(decl) => match &other.declarator {
        None => false,
        Some(other_decl) => decl.name().eq(&other_decl.name()),
      }
    }
  }
}

impl Eq for ParameterDeclaration { }

impl Ord for ParameterDeclaration {
  fn cmp(&self, other: &Self) -> Ordering {
    match &self.declarator {
      None => match other.declarator {
        None => Ordering::Equal,
        _ => Ordering::Less,
      },
      Some(decl) => match &other.declarator {
        None => Ordering::Greater,
        Some(other_decl) => decl.name().cmp(&other_decl.name()),
      }
    }
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
  ConstBool(bool),
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
  SketchHole,
  Ternary {
    condition: Box<Expression>,
    then: Box<Expression>,
    els:  Box<Expression>,
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
  Assert(Box<Expression>),
  Assume(Box<Expression>),
  BasicBlock(Vec<BlockItem>),
  Break,
  Compound(Vec<BlockItem>),
  Expression(Box<Expression>),
  GuardedRepeat {
    id: String,
    repetitions: usize,
    condition: Box<Expression>,
    body: Box<Statement>,
  },
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
    id: Uuid,
    runoff_link_id: Option<uuid::Uuid>,
    invariants: Vec<Expression>,
    condition: Box<Expression>,
    body: Option<Box<Statement>>,
    is_runoff: bool,
    is_merged: bool,
  },
  WhileRel {
    id: Uuid,
    unroll_left: usize,
    unroll_right: usize,
    stutter_left: usize,
    stutter_right: usize,
    invariants_left: Vec<Expression>,
    invariants_right: Vec<Expression>,
    condition_left: Box<Expression>,
    condition_right: Box<Expression>,
    body_left: Option<Box<Statement>>,
    body_right: Option<Box<Statement>>,
    body_merged: Option<Box<Statement>>,
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

  pub fn denote_while_rel(&self) -> Statement {
    match self {
      Statement::WhileRel {
        id,
        unroll_left,
        unroll_right,
        stutter_left,
        stutter_right,
        invariants_left,
        invariants_right,
        condition_left,
        condition_right,
        body_left,
        body_right,
        body_merged,
      } => {
        let condition_conj = Expression::Binop {
          lhs: condition_left.clone(),
          rhs: condition_right.clone(),
          op: BinaryOp::And,
        };
        let mut combined_invars: Vec<_> = invariants_left.clone();
        for expr in invariants_right {
          if !invariants_left.contains(expr) {
            combined_invars.push(expr.clone());
          }
        }
        let runoff_body_left = body_left.as_ref().map(|body_left| {
          Box::new(Statement::Compound(vec!(
            BlockItem::Statement(Statement::Assume(Box::new(
              Expression::Unop {
                expr: condition_right.clone(),
                op: UnaryOp::Not
              }))),
            BlockItem::Statement(*body_left.clone()))))
        });
        let runoff_body_right = body_right.as_ref().map(|body_right| {
          Box::new(Statement::Compound(vec!(
            BlockItem::Statement(Statement::Assume(Box::new(
              Expression::Unop {
                expr: condition_left.clone(),
                op: UnaryOp::Not
              }))),
            BlockItem::Statement(*body_right.clone()))))
        });
        let runoff_link_id = Some(uuid::Uuid::new_v4());

        let mut stutters = Vec::new();
        body_left.as_ref().map(|body_left| {
          for _ in 0..*stutter_left {
            stutters.push(BlockItem::Statement(Statement::If {
              condition: condition_left.clone(),
              then: body_left.clone(),
              els: None,
            }));
          }
        });
        body_right.as_ref().map(|body_right| {
          for _ in 0..*stutter_right {
            stutters.push(BlockItem::Statement(Statement::If {
              condition: condition_right.clone(),
              then: body_right.clone(),
              els: None,
            }));
          }
        });
        let body_with_stutters = if stutters.is_empty() {
          body_merged.clone()
        } else {
          body_merged.as_ref().map(|merged| {
            stutters.push(BlockItem::Statement(*merged.clone()))
          });
          Some(Box::new(Statement::Compound(stutters)))
        };

        let mut stmts = Vec::new();
        body_left.as_ref().map(|body_left| {
          for _ in 0..*unroll_left {
            stmts.push(BlockItem::Statement(Statement::If {
              condition: condition_left.clone(),
              then: body_left.clone(),
              els: None,
            }));
          }
        });
        body_right.as_ref().map(|body_right| {
          for _ in 0..*unroll_right {
            stmts.push(BlockItem::Statement(Statement::If {
              condition: condition_right.clone(),
              then: body_right.clone(),
              els: None,
            }));
          }
        });
        stmts.push(BlockItem::Statement(Statement::While {
          id: id.clone(),
          runoff_link_id: runoff_link_id.clone(),
          is_runoff: false,
          is_merged: true,
          invariants: combined_invars,
          condition: Box::new(condition_conj),
          body: body_with_stutters,
        }));
        stmts.push(BlockItem::Statement(Statement::If {
          condition: condition_left.clone(),
          then: Box::new(Statement::While {
            id: Uuid::new_v4(),
            runoff_link_id: runoff_link_id.clone(),
            is_runoff: true,
            is_merged: false,
            invariants: invariants_left.clone(),
            condition: condition_left.clone(),
            body: runoff_body_left,
          }),
          els: None,
        }));
        stmts.push(BlockItem::Statement(Statement::If {
          condition: condition_right.clone(),
          then: Box::new(Statement::While {
            id: Uuid::new_v4(),
            runoff_link_id: runoff_link_id.clone(),
            is_runoff: true,
            is_merged: false,
            invariants: invariants_right.clone(),
            condition: condition_right.clone(),
            body: runoff_body_right,
          }),
          els: None,
        }));
        Statement::Compound(stmts)
      },
      _ => panic!("Not a WhileRel: {:?}", self)
    }
  }
}

#[derive(Clone, Debug, PartialEq)]
pub enum BlockItem {
  Declaration(Declaration),
  Statement(Statement),
}

pub fn loop_head_name(id: &Uuid) -> String {
  format!("_loop_head_{}", id.to_string().replace("-", ""))
}
