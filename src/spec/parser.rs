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

fn cond_true(i: &str) -> IResult<&str, CondExpr> {
  let (i, _) = multispace0(i)?;
  let(i, _) = tag("true")(i)?;
  Ok((i, CondExpr::True))
}

fn cond_false(i: &str) -> IResult<&str, CondExpr> {
  let (i, _) = multispace0(i)?;
  let(i, _) = tag("false")(i)?;
  Ok((i, CondExpr::False))
}

fn cond_binop_a<'a, C>(op: &'a str, constr: &'a C) -> impl Fn(&str) -> IResult<&str, CondExpr> + 'a
  where C: Fn(Box<CondExpr>, Box<CondExpr>) -> CondExpr
{
  move |i: &str| {
    let (i, _)   = multispace0(i)?;
    let (i, lhs) = cond_aexpr(i)?;
    let (i, _)   = multispace0(i)?;
    let (i, _)   = tag(op)(i)?;
    let (i, _)   = multispace0(i)?;
    let (i, rhs) = cond_aexpr(i)?;
    Ok((i, constr(
      Box::new(lhs),
      Box::new(rhs),
    )))
  }
}

fn cond_binop_b<'a, C>(op: &'a str, constr: &'a C) -> impl Fn(&str) -> IResult<&str, CondExpr> + 'a
  where C: Fn(Box<CondExpr>, Box<CondExpr>) -> CondExpr
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


fn cond_eq(i: &str) -> IResult<&str, CondExpr> {
  cond_binop_a("==", &|lhs, rhs| CondExpr::Eq{lhs, rhs})(i)
}

fn cond_neq(i: &str) -> IResult<&str, CondExpr> {
  cond_binop_a("!=", &|lhs, rhs| CondExpr::Neq{lhs, rhs})(i)
}

fn cond_lt(i: &str) -> IResult<&str, CondExpr> {
  cond_binop_a("<", &|lhs, rhs| CondExpr::Lt{lhs, rhs})(i)
}

fn cond_lte(i: &str) -> IResult<&str, CondExpr> {
  cond_binop_a("<=", &|lhs, rhs| CondExpr::Lte{lhs, rhs})(i)
}

fn cond_gt(i: &str) -> IResult<&str, CondExpr> {
  cond_binop_a(">", &|lhs, rhs| CondExpr::Gt{lhs, rhs})(i)}

fn cond_gte(i: &str) -> IResult<&str, CondExpr> {
  cond_binop_a(">=", &|lhs, rhs| CondExpr::Gte{lhs, rhs})(i)
}

fn cond_and(i: &str) -> IResult<&str, CondExpr> {
  cond_binop_b("&&", &|lhs, rhs| CondExpr::And{lhs, rhs})(i)
}

fn cond_or(i: &str) -> IResult<&str, CondExpr> {
  cond_binop_b("||", &|lhs, rhs| CondExpr::Or{lhs, rhs})(i)
}

fn cond_not(i: &str) -> IResult<&str, CondExpr> {
  let (i, _)    = multispace0(i)?;
  let (i, _)    = tag("!")(i)?;
  let (i, expr) = cond_bexpr(i)?;
  Ok((i, CondExpr::Not(Box::new(expr))))
}

fn cond_fun(i: &str) -> IResult<&str, CondExpr> {
  let (i, _)    = multispace0(i)?;
  let (i, name) = c_id(i)?;
  Ok((i, CondExpr::Fun{name: name.to_string()}))
}

fn cond_var(i: &str) -> IResult<&str, CondExpr> {
  let (i, _)  = multispace0(i)?;
  let (i, id) = cond_id(i)?;
  Ok((i, CondExpr::Variable(id)))
}

fn cond_aexpr(i: &str) -> IResult<&str, CondExpr> {
  let (i, _) = multispace0(i)?;
  alt((
    cond_int,
    cond_var,
    cond_fun,
  ))(i)
}

fn cond_bexpr_lhs(i: &str) -> IResult<&str, CondExpr> {
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
    cond_var,
    cond_fun,
  ))(i)
}

fn cond_bexpr(i: &str) -> IResult<&str, CondExpr> {
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
    cond_var,
    cond_fun
  ))(i)
}

fn cond_int(i: &str) -> IResult<&str, CondExpr> {
  let (i, _) = multispace0(i)?;
  let (i, n) = i32(i)?;
  Ok((i, CondExpr::Int(n)))
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

fn pre(i: &str) -> IResult<&str, CondExpr> {
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

fn post(i: &str) -> IResult<&str, CondExpr> {
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
        * pre:   1.N == 2.N;
        * left:  fun;
        * right: fun;
        * post:  1.x == 2.x;
        */";
    let newlines = Regex::new(r"\n+").unwrap();
    let input = newlines.replace_all(input, " ");
    let expected_pre = CondExpr::Eq {
      lhs: Box::new(CondExpr::Variable(CondId{
        exec: "1".to_string(),
        name: "N".to_string() })),
      rhs: Box::new(CondExpr::Variable(CondId{
        exec: "2".to_string(),
        name: "N".to_string() })),
    };
    let expected_post = CondExpr::Eq {
      lhs: Box::new(CondExpr::Variable(CondId {
        exec: "1".to_string(),
        name: "x".to_string() })),
      rhs: Box::new(CondExpr::Variable(CondId {
        exec: "2".to_string(),
        name: "x".to_string() })),
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
