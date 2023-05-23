use crate::spec::{KestrelSpec, condition::*};
use nom::{
  branch::alt,
  bytes::complete::tag,
  character::complete::alpha1,
  character::complete::alphanumeric1,
  character::complete::i32,
  character::complete::multispace0,
  combinator::recognize,
  multi::many0_count,
  multi::many1_count,
  sequence::delimited,
  sequence::pair,
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

fn cond_true(i: &str) -> IResult<&str, CondBExpr> {
  let (i, _) = multispace0(i)?;
  let(i, _) = tag("true")(i)?;
  Ok((i, CondBExpr::True))
}

fn cond_false(i: &str) -> IResult<&str, CondBExpr> {
  let (i, _) = multispace0(i)?;
  let(i, _) = tag("false")(i)?;
  Ok((i, CondBExpr::False))
}

fn cond_binop_a<'a, C>(op: &'a str, constr: &'a C) -> impl Fn(&str) -> IResult<&str, CondBExpr> + 'a
  where C: Fn(CondAExpr, CondAExpr) -> CondBExpr
{
  move |i: &str| {
    let (i, _)   = multispace0(i)?;
    let (i, lhs) = cond_aexpr(i)?;
    let (i, _)   = multispace0(i)?;
    let (i, _)   = tag(op)(i)?;
    let (i, _)   = multispace0(i)?;
    let (i, rhs) = cond_aexpr(i)?;
    Ok((i, constr(lhs, rhs)))
  }
}

fn cond_binop_b<'a, C>(op: &'a str, constr: &'a C) -> impl Fn(&str) -> IResult<&str, CondBExpr> + 'a
  where C: Fn(Box<CondBExpr>, Box<CondBExpr>) -> CondBExpr
{
  move |i: &str| {
    let (i, _)   = multispace0(i)?;
    let (i, lhs) = cond_bexpr_lhs(i)?;
    let (i, _)   = multispace0(i)?;
    let (i, _)   = tag(op)(i)?;
    let (i, _)   = multispace0(i)?;
    let (i, rhs) = cond_bexpr(i)?;
    Ok((i, constr(
      Box::new(lhs),
      Box::new(rhs),
    )))
  }
}


fn cond_eq(i: &str) -> IResult<&str, CondBExpr> {
  cond_binop_a("==", &|lhs, rhs| CondBExpr::Eq{lhs, rhs})(i)
}

fn cond_neq(i: &str) -> IResult<&str, CondBExpr> {
  cond_binop_a("!=", &|lhs, rhs| CondBExpr::Neq{lhs, rhs})(i)
}

fn cond_lt(i: &str) -> IResult<&str, CondBExpr> {
  cond_binop_a("<", &|lhs, rhs| CondBExpr::Lt{lhs, rhs})(i)
}

fn cond_lte(i: &str) -> IResult<&str, CondBExpr> {
  cond_binop_a("<=", &|lhs, rhs| CondBExpr::Lte{lhs, rhs})(i)
}

fn cond_gt(i: &str) -> IResult<&str, CondBExpr> {
  cond_binop_a(">", &|lhs, rhs| CondBExpr::Gt{lhs, rhs})(i)}

fn cond_gte(i: &str) -> IResult<&str, CondBExpr> {
  cond_binop_a(">=", &|lhs, rhs| CondBExpr::Gte{lhs, rhs})(i)
}

fn cond_and(i: &str) -> IResult<&str, CondBExpr> {
  cond_binop_b("&&", &|lhs, rhs| CondBExpr::And{lhs, rhs})(i)
}

fn cond_or(i: &str) -> IResult<&str, CondBExpr> {
  cond_binop_b("||", &|lhs, rhs| CondBExpr::Or{lhs, rhs})(i)
}

fn cond_not(i: &str) -> IResult<&str, CondBExpr> {
  let (i, _)    = multispace0(i)?;
  let (i, _)    = tag("!")(i)?;
  let (i, expr) = cond_bexpr(i)?;
  Ok((i, CondBExpr::Not(Box::new(expr))))
}

fn cond_bexpr_lhs(i: &str) -> IResult<&str, CondBExpr> {
  let (i, _) = multispace0(i)?;
  alt((
    cond_true,
    cond_false,
    cond_not,
    cond_eq,
    cond_neq,
    cond_lte,
    cond_gte,
    cond_lt,
    cond_gt,
  ))(i)
}

fn cond_bexpr(i: &str) -> IResult<&str, CondBExpr> {
  let (i, _) = multispace0(i)?;
  alt((
    cond_true,
    cond_false,
    cond_and,
    cond_or,
    cond_not,
    cond_eq,
    cond_neq,
    cond_lte,
    cond_gte,
    cond_lt,
    cond_gt,
  ))(i)
}

fn cond_int(i: &str) -> IResult<&str, CondAExpr> {
  let (i, _) = multispace0(i)?;
  let (i, n) = i32(i)?;
  Ok((i, CondAExpr::Int(n)))
}

fn cond_var(i: &str) -> IResult<&str, CondAExpr> {
  let (i, _)  = multispace0(i)?;
  let (i, id) = cond_id(i)?;
  Ok((i, CondAExpr::Variable(id)))
}

fn cond_aexpr(i: &str) -> IResult<&str, CondAExpr> {
  let (i, _) = multispace0(i)?;
  alt((
    cond_int,
    cond_var,
  ))(i)
}

fn cond_id(i: &str) -> IResult<&str, CondId> {
  let (i, exec) = exec_id(i)?;
  let (i, _)    = tag(".")(i)?;
  let (i, name) = c_id(i)?;
  Ok((i, CondId { exec: exec.to_string(),
                  name: name.to_string() }))
}

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
    many0_count(alt((alphanumeric1, tag("_"))))
  ))(i)
}

fn semi(i: &str) -> IResult<&str, ()> {
  let (i, _)   = multispace0(i)?;
  let (i, _)   = tag(";")(i)?;
  Ok((i, ()))
}

fn pre(i: &str) -> IResult<&str, CondBExpr> {
  let (i, _)   = opt_asterisks(i)?;
  let (i, _)   = label("pre")(i)?;
  let (i, pre) = cond_bexpr(i)?;
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

fn post(i: &str) -> IResult<&str, CondBExpr> {
  let (i, _)    = opt_asterisks(i)?;
  let (i, _)    = label("post")(i)?;
  let (i, post) = cond_bexpr(i)?;
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

pub fn parse_spec(input_file: &String) -> Result<KestrelSpec, String> {
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
    let expected_pre = CondBExpr::Eq {
      lhs: CondAExpr::Variable(CondId{
        exec: "left".to_string(),
        name: "N".to_string() }),
      rhs: CondAExpr::Variable(CondId{
        exec: "right".to_string(),
        name: "N".to_string() }),
    };
    let expected_post = CondBExpr::Eq {
      lhs: CondAExpr::Variable(CondId {
        exec: "left".to_string(),
        name: "x".to_string() }),
      rhs: CondAExpr::Variable(CondId {
        exec: "right".to_string(),
        name: "x".to_string() }),
    };
    let expected = KestrelSpec {
      pre: expected_pre,
      left: "fun".to_string(),
      right: "fun".to_string(),
      post: expected_post,
    };
    assert_eq!(spec_comment(&input), Ok(("", expected)));
  }
}
