use crate::spec::{KestrelSpec, condition::*};
use nom::{
  branch::alt,
  bytes::complete::tag,
  character::complete::alpha1,
  character::complete::alphanumeric1,
  character::complete::digit1,
  character::complete::i32,
  character::complete::multispace0,
  combinator::recognize,
  error::{Error, ErrorKind},
  multi::many0,
  multi::many0_count,
  multi::many1,
  multi::many1_count,
  multi::separated_list0,
  multi::separated_list1,
  number::complete::float,
  sequence::delimited,
  sequence::pair,
  Err,
  IResult,
};
use regex::Regex;
use std::fs;

fn opt_asterisks(i: &str) -> IResult<&str, usize> {
  let (i, _)    = multispace0(i)?;
  let (i, asts) = many0_count(tag("*"))(i)?;
  Ok((i, asts))
}

fn label(label: &str) -> impl Fn(&str) -> IResult<&str, ()> + '_ {
  move |i: &str| {
    let (i, _) = multispace0(i)?;
    let (i, _) = tag(label)(i)?;
    let (i, _) = multispace0(i)?;
    let (i, _) = tag(":")(i)?;
    Ok((i, ()))
  }
}

fn semi(i: &str) -> IResult<&str, ()> {
  let (i, _)   = multispace0(i)?;
  let (i, _)   = tag(";")(i)?;
  Ok((i, ()))
}


/* Identifiers */

fn exec_id(i: &str) -> IResult<&str, &str> {
  let (i, _) = multispace0(i)?;
  recognize(
    many1_count(alt((alphanumeric1, tag("_")))
  ))(i)
}

fn c_id(i: &str) -> IResult<&str, &str> {
  let (i, _) = multispace0(i)?;
  recognize(pair(
    alt((alpha1, tag("_"))),
    many0(alt((alphanumeric1, tag("_"))))
  ))(i)
}


/* AExprs */

fn aexp_int(i: &str) -> IResult<&str, CondAExpr> {
  let (i, _) = multispace0(i)?;
  let (i, n) = i32(i)?;
  match dot_num(i) {
    Err(_) => Ok((i, CondAExpr::Int(n))),
    Ok(_) => Err(Err::Error(Error{input: i, code: ErrorKind::IsNot})),
  }
}
fn dot_num(i: &str) -> IResult<&str, ()> {
  let (i, _) = pair(tag("."), digit1)(i)?;
  Ok((i, ()))
}

fn aexp_float(i: &str) -> IResult<&str, CondAExpr> {
  let (i, _) = multispace0(i)?;
  let (i, f) = float(i)?;
  Ok((i, CondAExpr::Float(f)))
}

fn aexp_var(i: &str) -> IResult<&str, CondAExpr> {
  let (i, _)  = multispace0(i)?;
  let (i, id) = c_id(i)?;
  Ok((i, CondAExpr::Var(id.to_string())))
}

fn aexp_qualified_var(i: &str) -> IResult<&str, CondAExpr> {
  let (i, _)  = multispace0(i)?;
  let (i, exec) = exec_id(i)?;
  let (i, _)    = tag(".")(i)?;
  let (i, name) = c_id(i)?;
  Ok((i, CondAExpr::QualifiedVar {
    exec: exec.to_string(),
    name: name.to_string()}))
}

fn aexp_index(i: &str) -> IResult<&str, CondAExpr> {
  let (i, _)       = multispace0(i)?;
  let (i, id)      = alt((aexp_qualified_var,
                          aexp_var))(i)?;
  let (i, _)       = multispace0(i)?;
  let (i, indices) = many1(delimited(tag("["), aexpr_no_float, tag("]")))(i)?;
  let mut aexpr = CondAExpr::Binop {
    lhs: Box::new(id),
    rhs: Box::new(indices[0].clone()),
    op: CondABinop::Index,
  };
  for j in 1..indices.len() {
    aexpr = CondAExpr::Binop {
      lhs: Box::new(aexpr),
      rhs: Box::new(indices[j].clone()),
      op: CondABinop::Index,
    }
  }
  Ok((i, aexpr))
}

fn aexpr_binop(op_str: &str, op: CondABinop) -> impl Fn(&str) -> IResult<&str, CondAExpr> + '_ {
  move |i: &str| {
    let (i, _)   = multispace0(i)?;
    let (i, lhs) = aexpr_lhs(i)?;
    let (i, _)   = multispace0(i)?;
    let (i, _)   = tag(op_str)(i)?;
    let (i, _)   = multispace0(i)?;
    let (i, rhs) = aexpr(i)?;
    Ok((i, CondAExpr::Binop {
      lhs: Box::new(lhs),
      rhs: Box::new(rhs),
      op: op.clone(),
    }))
  }
}

fn aexp_funcall(i: &str) -> IResult<&str, CondAExpr> {
  let (i, _)         = multispace0(i)?;
  let (i, name)      = c_id(i)?;
  let (i, args)      = delimited(tag("("),
                                 separated_list0(tag(","), aexpr),
                                 tag(")"))(i)?;
  Ok((i, CondAExpr::FunCall{name: name.to_string(), args}))
}

fn aexpr_lhs(i: &str) -> IResult<&str, CondAExpr> {
  let (i, _) = multispace0(i)?;
  alt((
    aexp_int,
    aexp_float,
    aexp_funcall,
    aexp_index,
    aexp_qualified_var,
    aexp_var,
    delimited(tag("("), aexpr, tag(")")),
  ))(i)
}

pub fn aexpr(i: &str) -> IResult<&str, CondAExpr> {
  let (i, _) = multispace0(i)?;
  alt((
    aexpr_binop("+", CondABinop::Add),
    aexpr_binop("-", CondABinop::Sub),
    aexpr_binop("*", CondABinop::Mul),
    aexpr_binop("/", CondABinop::Div),
    aexpr_binop("%", CondABinop::Mod),
    aexp_int,
    aexp_float,
    aexp_funcall,
    aexp_index,
    aexp_qualified_var,
    aexp_var,
    delimited(tag("("), aexpr, tag(")")),
  ))(i)
}

fn aexpr_no_float(i: &str) -> IResult<&str, CondAExpr> {
  let (i, _) = multispace0(i)?;
  alt((
    aexpr_binop("+", CondABinop::Add),
    aexpr_binop("-", CondABinop::Sub),
    aexpr_binop("*", CondABinop::Mul),
    aexpr_binop("/", CondABinop::Div),
    aexpr_binop("%", CondABinop::Mod),
    aexp_int,
    aexp_index,
    aexp_funcall,
    aexp_qualified_var,
    aexp_var,
    delimited(tag("("), aexpr_no_float, tag(")")),
  ))(i)
}


/* BExprs */

fn bexpr_true(i: &str) -> IResult<&str, CondBExpr> {
  let (i, _) = multispace0(i)?;
  let(i, _) = tag("true")(i)?;
  Ok((i, CondBExpr::True))
}

fn bexpr_false(i: &str) -> IResult<&str, CondBExpr> {
  let (i, _) = multispace0(i)?;
  let(i, _) = tag("false")(i)?;
  Ok((i, CondBExpr::False))
}

fn bexpr_binop_a(op_str: &str, op: CondBBinopA) -> impl Fn(&str) -> IResult<&str, CondBExpr> + '_ {
  move |i: &str| {
    let (i, _)   = multispace0(i)?;
    let (i, lhs) = aexpr(i)?;
    let (i, _)   = multispace0(i)?;
    let (i, _)   = tag(op_str)(i)?;
    let (i, _)   = multispace0(i)?;
    let (i, rhs) = aexpr(i)?;
    Ok((i, CondBExpr::BinopA{lhs, rhs, op: op.clone()}))
  }
}

fn bexpr_binop_b(op_str: &str, op: CondBBinopB) -> impl Fn(&str) -> IResult<&str, CondBExpr> + '_ {
  move |i: &str| {
    let (i, _)   = multispace0(i)?;
    let (i, lhs) = bexpr_lhs(i)?;
    let (i, _)   = multispace0(i)?;
    let (i, _)   = tag(op_str)(i)?;
    let (i, _)   = multispace0(i)?;
    let (i, rhs) = bexpr(i)?;
    Ok((i, CondBExpr::BinopB{lhs: Box::new(lhs), rhs: Box::new(rhs) , op: op.clone()}))
  }
}

fn bexpr_unop(op_str: &str, op: CondBUnop) -> impl Fn(&str) -> IResult<&str, CondBExpr> + '_ {
  move |i: &str| {
    let (i, _)    = multispace0(i)?;
    let (i, _)    = tag(op_str)(i)?;
    let (i, _)    = multispace0(i)?;
    let (i, expr) = bexpr(i)?;
    Ok((i, CondBExpr::Unop{bexp: Box::new(expr), op: op.clone()}))
  }
}

fn bexpr_forall(i: &str) -> IResult<&str, CondBExpr> {
  let (i, _)         = multispace0(i)?;
  let (i, _)         = tag("forall")(i)?;
  let (i, _)         = multispace0(i)?;
  let (i, bindings)  = separated_list1(tag(","), bexpr_forall_binding)(i)?;
  let (i, _)         = multispace0(i)?;
  let (i, _)         = tag("::")(i)?;
  let (i, _)         = multispace0(i)?;
  let (i, condition) = bexpr(i)?;
  Ok((i, CondBExpr::Forall {
    bindings,
    condition: Box::new(condition)
  }))
}

fn bexpr_forall_binding(i: &str) -> IResult<&str, (String, KestrelType)> {
  let (i, _)         = multispace0(i)?;
  let (i, pred_var)  = c_id(i)?;
  let (i, _)         = multispace0(i)?;
  let (i, _)         = tag(":")(i)?;
  let (i, _)         = multispace0(i)?;
  let (i, pred_type) = alpha1(i)?;
  match pred_type {
    "float" => Ok((i, (pred_var.to_string(), KestrelType::Float))),
    "int"   => Ok((i, (pred_var.to_string(), KestrelType::Int))),
    _ => Err(Err::Error(Error{input: i, code: ErrorKind::Fail})),
  }
}

fn bexpr_predicate(i: &str) -> IResult<&str, CondBExpr> {
  let (i, _)         = multispace0(i)?;
  let (i, name)      = c_id(i)?;
  let (i, args)      = delimited(tag("("),
                                 separated_list0(tag(","), aexpr),
                                 tag(")"))(i)?;
  Ok((i, CondBExpr::Predicate{name: name.to_string(), args}))
}

fn bexpr_lhs(i: &str) -> IResult<&str, CondBExpr> {
  let (i, _) = multispace0(i)?;
  alt((
    bexpr_true,
    bexpr_false,
    bexpr_unop("!", CondBUnop::Not),
    bexpr_binop_a("==", CondBBinopA::Eq),
    bexpr_binop_a("!=", CondBBinopA::Neq),
    bexpr_binop_a("<", CondBBinopA::Lt),
    bexpr_binop_a("<=", CondBBinopA::Lte),
    bexpr_binop_a(">", CondBBinopA::Gt),
    bexpr_binop_a(">=", CondBBinopA::Gte),
    bexpr_forall,
    bexpr_predicate,
    delimited(tag("("), bexpr, tag(")")),
  ))(i)
}

pub fn bexpr(i: &str) -> IResult<&str, CondBExpr> {
  let (i, _) = multispace0(i)?;
  alt((
    bexpr_binop_b("&&",  CondBBinopB::And),
    bexpr_binop_b("||",  CondBBinopB::Or),
    bexpr_binop_b("==>", CondBBinopB::Implies),
    bexpr_lhs,
    delimited(tag("("), bexpr, tag(")")),
  ))(i)
}


/* KestrelConds */

fn kcond_loop(i: &str) -> IResult<&str, KestrelCond> {
  let (i, _)     = multispace0(i)?;
  let (i, _)     = tag("for")(i)?;
  let (i, _)     = multispace0(i)?;
  let (i, var)   = c_id(i)?;
  let (i, _)     = multispace0(i)?;
  let (i, _)     = tag("in")(i)?;
  let (i, _)     = multispace0(i)?;
  let (i, _)     = tag("(")(i)?;
  let (i, _)     = multispace0(i)?;
  let (i, start) = aexpr_no_float(i)?;
  let (i, _)     = multispace0(i)?;
  let (i, _)     = tag("..")(i)?;
  let (i, _)     = multispace0(i)?;
  let (i, end)   = aexpr_no_float(i)?;
  let (i, _)     = multispace0(i)?;
  let (i, _)     = tag(")")(i)?;
  let (i, _)     = multispace0(i)?;
  let (i, _)     = tag("{")(i)?;
  let (i, _)     = multispace0(i)?;
  let (i, body)  = kestrel_cond(i)?;
  let (i, _)     = multispace0(i)?;
  let (i, _)     = tag("}")(i)?;
  Ok((i, KestrelCond::ForLoop{index_var: var.to_string(), start, end, body: Box::new(body)}))
}

fn kcond_and(i: &str) -> IResult<&str, KestrelCond> {
  let (i, _)   = multispace0(i)?;
  let (i, lhs) = alt((kcond_loop, kcond_bexpr))(i)?;
  let (i, _)   = multispace0(i)?;
  let (i, _)   = tag("&&")(i)?;
  let (i, _)   = multispace0(i)?;
  let (i, rhs) = kestrel_cond(i)?;
  Ok((i, KestrelCond::And{lhs: Box::new(lhs), rhs: Box::new(rhs)}))
}

fn kcond_bexpr(i: &str) -> IResult<&str, KestrelCond> {
  let (i, bexpr) = bexpr(i)?;
  Ok((i, KestrelCond::BExpr(bexpr)))
}

pub fn kestrel_cond(i: &str) -> IResult<&str, KestrelCond> {
  alt((
    kcond_and,
    kcond_bexpr,
    kcond_loop,
  ))(i)
}


/* Kestrel Specs */

fn pre(i: &str) -> IResult<&str, KestrelCond> {
  let (i, _)   = opt_asterisks(i)?;
  let (i, _)   = label("pre")(i)?;
  let (i, pre) = kestrel_cond(i)?;
  let (i, _)   = semi(i)?;
  Ok((i, pre))
}

fn left(i: &str) -> IResult<&str, String> {
  let (i, _)    = opt_asterisks(i)?;
  let (i, _)    = multispace0(i)?;
  let (i, _)    = label("left")(i)?;
  let (i, left) = c_id(i)?;
  let (i, _)    = semi(i)?;
  Ok((i, left.to_string()))
}

fn right(i: &str) -> IResult<&str, String> {
  let (i, _)     = opt_asterisks(i)?;
  let (i, _)     = multispace0(i)?;
  let (i, _)     = label("right")(i)?;
  let (i, right) = c_id(i)?;
  let (i, _)     = semi(i)?;
  Ok((i, right.to_string()))
}

fn post(i: &str) -> IResult<&str, KestrelCond> {
  let (i, _)    = opt_asterisks(i)?;
  let (i, _)    = label("post")(i)?;
  let (i, post) = kestrel_cond(i)?;
  let (i, _)    = semi(i)?;
  Ok((i, post))
}

fn kestrel_spec(i: &str) -> IResult<&str, KestrelSpec> {
  let (i, _)     = multispace0(i)?;
  let (i, _)     = tag("@KESTREL")(i)?;
  let (i, _)     = multispace0(i)?;
  let (i, pre)   = pre(i)?;
  let (i, left)  = left(i)?;
  let (i, right) = right(i)?;
  let (i, post)  = post(i)?;
  let (i, _)     = multispace0(i)?;
  let kspec = KestrelSpec{ pre, left, right, post };
  Ok((i, kspec))
}

fn spec_comment(i: &str) -> IResult<&str, KestrelSpec> {
  let (i, _) = multispace0(i)?;
  delimited(tag("/*"), kestrel_spec, tag("*/"))(i)
}

pub fn parse_kestrel_spec(input_file: &String) -> Result<KestrelSpec, String> {
  match fs::read_to_string(input_file) {
    Err(err) => Err(err.to_string()),
    Ok(input) => {
      let newlines = Regex::new(r"\n+").unwrap();
      let input = newlines.replace_all(input.as_str(), " ");
      match spec_comment(&input) {
        Ok((_, result)) => Ok(result),
        Err(e) => Err(e.to_string()),
      }
    }
  }
}

#[cfg(test)]
mod test {
  use super::*;

  #[test]
  fn test_spec_comment() {
    let input =
      "/* @KESTREL
        * pre:   left.N == right.N;
        * left:  fun;
        * right: fun;
        * post:  left.x == right.x;
        */";
    let newlines = Regex::new(r"\n+").unwrap();
    let input = newlines.replace_all(input, " ");
    let expected_pre = KestrelCond::BExpr(CondBExpr::BinopA {
      lhs: CondAExpr::QualifiedVar{
        exec: "left".to_string(),
        name: "N".to_string(),
      },
      rhs: CondAExpr::QualifiedVar{
        exec: "right".to_string(),
        name: "N".to_string()
      },
      op: CondBBinopA::Eq,
    });
    let expected_post = KestrelCond::BExpr(CondBExpr::BinopA {
      lhs: CondAExpr::QualifiedVar {
        exec: "left".to_string(),
        name: "x".to_string()
      },
      rhs: CondAExpr::QualifiedVar {
        exec: "right".to_string(),
        name: "x".to_string()
      },
      op: CondBBinopA::Eq,
    });
    let expected = KestrelSpec {
      pre: expected_pre,
      left: "fun".to_string(),
      right: "fun".to_string(),
      post: expected_post,
    };
    assert_eq!(spec_comment(&input), Ok(("", expected)));
  }

  #[test]
  fn test_bexpr_and() {
    let input = "a < b && x >= y";
    let expected = CondBExpr::BinopB {
      lhs: Box::new(CondBExpr::BinopA {
        lhs: CondAExpr::Var("a".to_string()),
        rhs: CondAExpr::Var("b".to_string()),
        op: CondBBinopA:: Lt,
      }),
      rhs: Box::new(CondBExpr::BinopA {
        lhs: CondAExpr::Var("x".to_string()),
        rhs: CondAExpr::Var("y".to_string()),
        op: CondBBinopA::Gte,
      }),
      op: CondBBinopB::And
    };
    assert_eq!(bexpr(input), Ok(("", expected)));
  }

  #[test]
  fn test_abinop_example1() {
    let input = "a_1 - a_2";
    let a_1 = CondAExpr::Var("a_1".to_string());
    let a_2 = CondAExpr::Var("a_2".to_string());
    let expected = CondAExpr::Binop {
      lhs: Box::new(a_1),
      rhs: Box::new(a_2),
      op: CondABinop::Sub,
    };
    assert_eq!(aexpr(input), Ok(("", expected)));
  }

  #[test]
  fn test_bbinop_example1() {
    let input = "a_1 - a_2 < epsilon";
    let a_1 = CondAExpr::Var("a_1".to_string());
    let a_2 = CondAExpr::Var("a_2".to_string());
    let expected = CondBExpr::BinopA {
      lhs: CondAExpr::Binop {
        lhs: Box::new(a_1),
        rhs: Box::new(a_2),
        op: CondABinop::Sub,
      },
      rhs: CondAExpr::Var("epsilon".to_string()),
      op: CondBBinopA:: Lt,
    };
    assert_eq!(bexpr(input), Ok(("", expected)));
  }

  #[test]
  fn test_bbinop_example2() {
    let input = "(a_1 >= a_2 && a_1 - a_2 < epsilon)";
    let a_1 = CondAExpr::Var("a_1".to_string());
    let a_2 = CondAExpr::Var("a_2".to_string());
    let expected = CondBExpr::BinopB {
      lhs: Box::new(CondBExpr::BinopA {
        lhs: a_1.clone(),
        rhs: a_2.clone(),
        op: CondBBinopA:: Gte,
      }),
      rhs: Box::new(CondBExpr::BinopA {
        lhs: CondAExpr::Binop {
          lhs: Box::new(a_1),
          rhs: Box::new(a_2),
          op: CondABinop::Sub,
        },
        rhs: CondAExpr::Var("epsilon".to_string()),
        op: CondBBinopA:: Lt,
      }),
      op: CondBBinopB::And
    };
    assert_eq!(bexpr(input), Ok(("", expected)));
  }

  #[test]
  fn test_bbinop_example3() {
    let input = "(a_1[i] >= a_2[i] && a_1[i] - a_2[i] < epsilon)";
    let a_1_i = CondAExpr::Binop {
      lhs: Box::new(CondAExpr::Var("a_1".to_string())),
      rhs: Box::new(CondAExpr::Var("i".to_string())),
      op: CondABinop::Index,
    };
    let a_2_i = CondAExpr::Binop {
      lhs: Box::new(CondAExpr::Var("a_2".to_string())),
      rhs: Box::new(CondAExpr::Var("i".to_string())),
      op: CondABinop::Index,
    };
    let expected = CondBExpr::BinopB {
      lhs: Box::new(CondBExpr::BinopA {
        lhs: a_1_i.clone(),
        rhs: a_2_i.clone(),
        op: CondBBinopA:: Gte,
      }),
      rhs: Box::new(CondBExpr::BinopA {
        lhs: CondAExpr::Binop {
          lhs: Box::new(a_1_i),
          rhs: Box::new(a_2_i),
          op: CondABinop::Sub,
        },
        rhs: CondAExpr::Var("epsilon".to_string()),
        op: CondBBinopA:: Lt,
      }),
      op: CondBBinopB::And
    };
    assert_eq!(bexpr(input), Ok(("", expected)));
  }

  #[test]
  fn test_loop() {
    let input = "for i in (0..5) { a_1[i] >= a_2[i] && b_1[i] < b_2[i] }";
    let a_1_i = CondAExpr::Binop {
      lhs: Box::new(CondAExpr::Var("a_1".to_string())),
      rhs: Box::new(CondAExpr::Var("i".to_string())),
      op: CondABinop::Index,
    };
    let a_2_i = CondAExpr::Binop {
      lhs: Box::new(CondAExpr::Var("a_2".to_string())),
      rhs: Box::new(CondAExpr::Var("i".to_string())),
      op: CondABinop::Index,
    };
    let b_1_i = CondAExpr::Binop {
      lhs: Box::new(CondAExpr::Var("b_1".to_string())),
      rhs: Box::new(CondAExpr::Var("i".to_string())),
      op: CondABinop::Index,
    };
    let b_2_i = CondAExpr::Binop {
      lhs: Box::new(CondAExpr::Var("b_2".to_string())),
      rhs: Box::new(CondAExpr::Var("i".to_string())),
      op: CondABinop::Index,
    };
    let expected = KestrelCond::ForLoop {
      index_var: "i".to_string(),
      start: CondAExpr::Int(0),
      end: CondAExpr::Int(5),
      body: Box::new(KestrelCond::BExpr(CondBExpr::BinopB {
        lhs: Box::new(CondBExpr::BinopA {
          lhs: a_1_i.clone(),
          rhs: a_2_i.clone(),
          op: CondBBinopA::Gte,
        }),
        rhs: Box::new(CondBExpr::BinopA {
          lhs: b_1_i.clone(),
          rhs: b_2_i.clone(),
          op: CondBBinopA::Lt,
        }),
        op: CondBBinopB::And,
      }))
    };
    assert_eq!(kestrel_cond(input), Ok(("", expected)));
  }

  #[test]
  fn test_nested_loop() {
    let input = "for i in (0..5) { for j in (1..10) { a[i] == a[j] } }";
    let a_i = CondAExpr::Binop {
      lhs: Box::new(CondAExpr::Var("a".to_string())),
      rhs: Box::new(CondAExpr::Var("i".to_string())),
      op: CondABinop::Index,
    };
    let a_j = CondAExpr::Binop {
      lhs: Box::new(CondAExpr::Var("a".to_string())),
      rhs: Box::new(CondAExpr::Var("j".to_string())),
      op: CondABinop::Index,
    };
    let expected = KestrelCond::ForLoop {
      index_var: "i".to_string(),
      start: CondAExpr::Int(0),
      end: CondAExpr::Int(5),
      body: Box::new(KestrelCond::ForLoop {
        index_var: "j".to_string(),
        start: CondAExpr::Int(1),
        end: CondAExpr::Int(10),
        body: Box::new(KestrelCond::BExpr(CondBExpr::BinopA {
          lhs: a_i,
          rhs: a_j,
          op: CondBBinopA::Eq,
        })),
      }),
    };
    assert_eq!(kestrel_cond(input), Ok(("", expected)));
  }

  #[test]
  fn test_2d_index() {
    let input = "a[i][j]";
    let expected = CondAExpr::Binop {
      lhs: Box::new(CondAExpr::Binop {
        lhs: Box::new(CondAExpr::Var("a".to_string())),
        rhs: Box::new(CondAExpr::Var("i".to_string())),
        op: CondABinop::Index,
      }),
      rhs: Box::new(CondAExpr::Var("j".to_string())),
      op: CondABinop::Index,
    };
    assert_eq!(aexpr(input), Ok(("", expected)));
  }
}
