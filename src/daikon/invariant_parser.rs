use crate::spec::condition::*;
use crate::spec::parser::*;
use nom :: {
  branch::alt,
  bytes::complete::take_until,
  bytes::complete::tag,
  character::complete::alpha1,
  character::complete::alphanumeric1,
  character::complete::multispace0,
  combinator::recognize,
  multi::many0,
  multi::many1,
  sequence::pair,
  IResult,
};
use std::collections::HashMap;

type InvariantMap = HashMap<String, Vec<CondBExpr>>;

fn skip_to_eq_bar(i: &str) -> IResult<&str, &str> {
  let (i, _) = multispace0(i)?;
  let (i, text) = take_until("=====")(i)?;
  Ok((i, text))
}

fn eq_bar(i: &str) -> IResult<&str, ()> {
  let (i, _) = multispace0(i)?;
  let (i, _) = many1(tag("="))(i)?;
  Ok((i, ()))
}

fn section(i: &str) -> IResult<&str, &str> {
  let (i, _) = multispace0(i)?;
  let (i, _) = eq_bar(i)?;
  let (i, text) = skip_to_eq_bar(i)?;
  Ok((i, text))
}

fn loop_id(i: &str) -> IResult<&str, &str> {
  let (i, _) = multispace0(i)?;
  recognize(pair(
    alt((alpha1, tag("_"))),
    many0(alt((alphanumeric1, tag("_"))))
  ))(i)
}

fn invars(i: &str) -> IResult<&str, (String, Vec<CondBExpr>)> {
  let (i, _) = multispace0(i)?;
  let (i, _) = tag("..")(i)?;
  let (i, name) = loop_id(i)?;
  let (i, _) = tag("():::ENTER")(i)?;
  let (body, _) = multispace0(i)?;
  let invars = body.lines()
    .map(|line| match bexpr(line) {
      Ok((_, cond)) => Some(cond),
      _ => None,
    })
    .filter(|mcond| mcond.is_some())
    .map(|cond| cond.unwrap())
    .collect();
  Ok((i, (name.to_string(), invars)))
}

fn parse_daikon_output(i: &str) -> IResult<&str, InvariantMap> {
  let (i, _) = skip_to_eq_bar(i)?;
  let (i, sections) = many1(section)(i)?;
  let invars = sections.iter()
    .map(|i| match invars(i) {
      Ok((_, item)) => Some(item),
      _ => None,
    })
    .filter(|i| i.is_some())
    .map(|i| i.unwrap())
    .collect();
  Ok((i, invars))
}

pub fn parse_invariants(daikon_output: &str) -> Result<InvariantMap, String> {
  match parse_daikon_output(daikon_output) {
    Ok((_, result)) => Ok(result),
    Err(err) => Err(err.to_string()),
  }
}
