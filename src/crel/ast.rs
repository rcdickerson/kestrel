#[derive(Clone, Debug)]
pub enum CRel {
  ConstInt(i32),
  Asgn {
    lhs: Box<CRel>,
    rhs: Box<CRel>,
  },
  Init {
    var: Box<CRel>,
    val: Option<Box<CRel>>,
  },
  If {
    cond: Box<CRel>,
    br_then: Box<CRel>,
    br_else: Box<CRel>,
  },
  While {
    cond: Box<CRel>,
    body: Box<CRel>,
  },
  Seq(Vec<CRel>),
  Id(String),
  Return(Box<CRel>),
  Declaration {
    specifiers: Vec<CRelSpecifier>,
    declarators: Vec<CRel>,
  },
  FunDef {
    specifiers: Vec<CRelSpecifier>,
    name: String,
    args: Vec<CRel>,
    body: Box<CRel>,
  },
  Call {
    callee: String,
    args: Vec<CRel>,
  },
  Rel {
    lhs: Box<CRel>,
    rhs: Box<CRel>
  },
  Lte(Box<CRel>, Box<CRel>),
  Eq(Box<CRel>, Box<CRel>),
  Add(Box<CRel>, Box<CRel>),
  Skip,
  Uninterp(String),
}

#[derive(Clone, Debug)]
pub enum CRelSpecifier {
  TypeSpecifier(CRelType),
  Uninterp(String),
}

#[derive(Clone, Debug)]
pub enum CRelType {
  Float,
  Int,
  Void,
  Uninterp(String),
}
