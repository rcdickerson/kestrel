use nom::{
  bytes::complete::tag,
  bytes::complete::take_until,
  character::complete::space0,
  multi::many0_count,
  sequence::delimited,
  IResult,
};
use regex::Regex;
use std::fs;

#[derive(Clone, Debug, PartialEq)]
pub struct KestrelSpec {
  pre: String,
  left: String,
  right: String,
  post: String,
}

fn opt_asterisks(i: &str) -> IResult<&str, usize> {
  let (i, _)    = space0(i)?;
  let (i, asts) = many0_count(tag("*"))(i)?;
  Ok((i, asts))
}

fn labeled(label: &str) -> impl Fn(&str) -> IResult<&str, &str> + '_ {
  move |i: &str| {
    let (i, _)      = opt_asterisks(i)?;
    let (i, _)      = space0(i)?;
    let (i, _)      = tag(label)(i)?;
    let (i, _)      = space0(i)?;
    let (i, _)      = tag(":")(i)?;
    let (i, _)      = space0(i)?;
    let (i, result) = take_until(";")(i)?;
    let (i, _)      = tag(";")(i)?;
    Ok((i, result))
  }
}

fn pre(i: &str) -> IResult<&str, &str> {
  let (i, _)       = opt_asterisks(i)?;
  let (i, pre_str) = labeled("pre")(i)?;
  Ok((i, pre_str))
}

fn left(i: &str) -> IResult<&str, &str> {
  let (i, _) = opt_asterisks(i)?;
  let (i, left_str) = labeled("left")(i)?;
  Ok((i, left_str))
}

fn right(i: &str) -> IResult<&str, &str> {
  let (i, _) = opt_asterisks(i)?;
  let (i, right_str) = labeled("right")(i)?;
  Ok((i, right_str))
}

fn post(i: &str) -> IResult<&str, &str> {
  let (i, _) = opt_asterisks(i)?;
  let (i, post_str) = labeled("post")(i)?;
  Ok((i, post_str))
}

fn kestrel_spec(i: &str) -> IResult<&str, KestrelSpec> {
  let (i, _)     = space0(i)?;
  let (i, _)     = tag("@KESTREL")(i)?;
  let (i, _)     = space0(i)?;
  let (i, pre)   = pre(i)?;
  let (i, left)  = left(i)?;
  let (i, right) = right(i)?;
  let (i, post)  = post(i)?;
  let (i, _)     = space0(i)?;
  let kspec = KestrelSpec{
    pre: pre.to_string(),
    left: left.to_string(),
    right: right.to_string(),
    post: post.to_string(),
  };
  Ok((i, kspec))
}

fn spec_comment(i: &str) -> IResult<&str, KestrelSpec> {
  let (i, _) = space0(i)?;
  delimited(tag("/*"), kestrel_spec, tag("*/"))(i)
}

fn parse_spec(input_file: String) -> Result<KestrelSpec, String> {
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
    let expected = KestrelSpec {
      pre: "1.N == 2.N".to_string(),
      left: "fun".to_string(),
      right: "fun".to_string(),
      post: "1.x == 2.x".to_string(),
    };
    assert_eq!(spec_comment(&input), Ok(("", expected)));
  }
}
