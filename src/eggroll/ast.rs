use egg::*;

define_language! {
  pub enum Eggroll {
    // Arithmetic Expressions
    "+"   = Add([Id; 2]),
    "-"   = Sub([Id; 2]),
    "*"   = Mul([Id; 2]),
    "/"   = Div([Id; 2]),
    "mod" = Mod([Id; 2]),
    "neg" = Neg(Id),

    // Boolean Expressions
    "<"   = Lt([Id; 2]),
    "<="  = Lte([Id; 2]),
    ">"   = Gt([Id; 2]),
    ">="  = Gte([Id; 2]),
    "=="  = Eq([Id; 2]),
    "!="  = Neq([Id; 2]),
    "&&"  = And([Id; 2]),
    "||"  = Or([Id; 2]),
    "not" = Not(Id),

    // Expressions
    "="             = Asgn([Id; 2]),
    "if"            = If([Id; 2]),
    "if-else"       = IfElse([Id; 3]),
    "while"         = While([Id; 2]),
    "while-double"  = WhileDouble([Id; 2]),
    "while-no-body" = WhileNoBody([Id; 1]),
    "index"         = Index([Id; 2]),
    "seq"           = Seq([Id; 2]),
    "assert"        = Assert(Id),
    "break"         = Break,

    // An abbreviated form of :
    //   while c1 && c2 { b1; b2 };
    //   while c1 b1;
    //   while c2 b2;
    // We use this form to rewrite to aligned while
    // loops without introducing lots of AST nodes
    // which inflates the cost of the alignment.
    // This makes the cost function simpler at the
    // expense of making the rewrite rules more
    // complicated if we ever want to rewrite within
    // the expanded form. Currently we do not need to
    // make these kinds of rewrites within the
    // expanded form, but we may want to revisit this
    // tradeoff in the future.
    "while-lockstep" = WhileLockstep([Id; 6]),

    // Declarations
    "declaration" = Declaration([Id; 2]),
    "init-declarator" = InitDeclarators([Id; 2]),
    "fun-declarator" = FunDeclarator([Id; 2]),
    "sized-array" = SizedArray([Id; 2]),
    "unsized-array" = UnsizedArray(Id),
    "pointer" = Pointer(Id),
    "specifiers" = Specifiers(Box<[Id]>),
    "declarators" = Declarators(Box<[Id]>),
    "type" = Type(Id),
    "type-qualifier" = TypeQualifier(Id),
    "storage-class" = StorageClass(Id),

    // Functions
    "call"        = Call(Box<[Id]>),
    "fundef"      = FunDef([Id; 4]),
    "args"        = Args(Box<[Id]>),
    "params"      = Params(Box<[Id]>),
    "body"        = Body(Id),
    "return-none" = ReturnNone,
    "return"      = Return(Id),

    // Tagged basic blocks (straight-line code will not be rewritten)
    "basic-block" = BasicBlock(Box<[Id]>),

    // Literals
    ConstInt(i32),
    Identifier(Symbol),
    "lit-string" = LitString(Id),

    // Relational Constructions
    "<|>" = Rel([Id; 2]),
    "<|"  = RelLeft(Id),
    "|>"  = RelRight(Id),
  }
}
