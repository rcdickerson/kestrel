use egg::*;

define_language! {
  pub enum Eggroll {
    // Arithmetic Expressions
    "+"   = Add([Id; 2]),
    "-"   = Sub([Id; 2]),
    "*"   = Mul([Id; 2]),
    "/"   = Div([Id; 2]),
    "mod" = Mod([Id; 2]),

    // Boolean Expressions
    "<"   = Lt([Id; 2]),
    "<="  = Lte([Id; 2]),
    ">"   = Gt([Id; 2]),
    ">="  = Gte([Id; 2]),
    "=="  = Eq([Id; 2]),
    "&&"  = And([Id; 2]),
    "||"  = Or([Id; 2]),
    "not" = Not(Id),

    // Expressions
    "="       = Asgn([Id; 2]),
    "if"      = If([Id; 2]),
    "if-else" = IfElse([Id; 3]),
    "while"   = While([Id; 2]),
    "seq"     = Seq([Id; 2]),
    "assert"  = Assert(Id),

    // Declarations
    "declaration" = Declaration([Id; 2]),
    "init-declarator" = InitDeclarators([Id; 2]),
    "specifiers" = Specifiers(Box<[Id]>),
    "declarators" = Declarators(Box<[Id]>),
    "type" = Type(Id),
    "storage-class" = StorageClass(Id),

    // Functions
    "call"        = Call(Box<[Id]>),
    "fundef"      = FunDef([Id; 4]),
    "args"        = Args(Box<[Id]>),
    "params"      = Params(Box<[Id]>),
    "body"        = Body(Id),
    "return-none" = ReturnNone,
    "return"      = Return(Id),

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
