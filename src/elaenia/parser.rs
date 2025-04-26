use crate::elaenia::elaenia_spec::*;
use crate::spec::condition::*;
use crate::spec::parser::kestrel_cond;
use nom::{
  branch::alt,
  bytes::complete::tag,
  character::complete::alpha1,
  character::complete::alphanumeric1,
  character::complete::u32,
  character::complete::multispace0,
  combinator::opt,
  combinator::recognize,
  multi::many0,
  multi::separated_list0,
  sequence::delimited,
  sequence::pair,
  IResult,
};
use regex::Regex;
use std::fs;

fn label(label: &str) -> impl Fn(&str) -> IResult<&str, ()> + '_ {
  move |i: &str| {
    let (i, _) = multispace0(i)?;
    let (i, _) = tag(label)(i)?;
    let (i, _) = multispace0(i)?;
    let (i, _) = tag(":")(i)?;
    Ok((i, ()))
  }
}

fn c_id(i: &str) -> IResult<&str, &str> {
  let (i, _) = multispace0(i)?;
  recognize(pair(
    alt((alpha1, tag("_"))),
    many0(alt((alphanumeric1, tag("_"))))
  ))(i)
}

fn parameter(i: &str) -> IResult<&str, Parameter> {
  let (i, _) = multispace0(i)?;
  let (i, name ) = c_id(i)?;
  let (i, sizes) = many0(delimited(tag("["), u32, tag("]")))(i)?;
  Ok((i, {
    let mut param = Parameter::Variable(name.to_string());
    for size in sizes {
      param = Parameter::Array{ lhs: Box::new(param), size }
    }
    param
  }))
}

fn semi(i: &str) -> IResult<&str, ()> {
  let (i, _) = multispace0(i)?;
  let (i, _) = tag(";")(i)?;
  Ok((i, ()))
}

fn pre(i: &str) -> IResult<&str, KestrelCond> {
  let (i, _)    = label("pre")(i)?;
  let (i, cond) = kestrel_cond(i)?;
  let (i, _)    = semi(i)?;
  Ok((i, cond))
}

fn forall(i: &str) -> IResult<&str, String> {
  let (i, _)    = label("forall")(i)?;
  let (i, _)    = multispace0(i)?;
  let (i, afun) = c_id(i)?;
  let (i, _)    = multispace0(i)?;
  let (i, _)    = semi(i)?;
  Ok((i, afun.to_string()))
}

fn exists(i: &str) -> IResult<&str, String> {
  let (i, _)    = label("exists")(i)?;
  let (i, _)    = multispace0(i)?;
  let (i, efun) = c_id(i)?;
  let (i, _)    = multispace0(i)?;
  let (i, _)    = semi(i)?;
  Ok((i, efun.to_string()))
}

fn post(i: &str) -> IResult<&str, KestrelCond> {
  let (i, _)    = label("post")(i)?;
  let (i, cond) = kestrel_cond(i)?;
  let (i, _)   = semi(i)?;
  Ok((i, cond))
}

fn universal_spec(i: &str) -> IResult<&str, UniversalSpec> {
  let (i, name)   = c_id(i)?;
  let (i, _)      = multispace0(i)?;
  let (i, params) = delimited(tag("("),
                              separated_list0(tag(","), parameter),
                              tag(")"))(i)?;
  let (i, _)      = multispace0(i)?;
  let (i, _)      = tag("{")(i)?;
  let (i, _)      = multispace0(i)?;
  let (i, pre)    = pre(i)?;
  let (i, _)      = multispace0(i)?;
  let (i, post)   = post(i)?;
  let (i, _)      = multispace0(i)?;
  let (i, _)      = tag("}")(i)?;
  Ok((i, UniversalSpec {
    name: name.to_string(),
    params,
    pre,
    post,
  }))
}

fn universal_specs(i: &str) -> IResult<&str, Vec<UniversalSpec>> {
  let (i, _) = label("aspecs")(i)?;
  many0(universal_spec)(i)
}

fn choice_vars(i: &str) -> IResult<&str, Vec<String>> {
  let (i, _)    = label("choiceVars")(i)?;
  let (i, vars) = separated_list0(tag(","), c_id)(i)?;
  let (i, _)    = semi(i)?;
  Ok((i, vars.iter().map(|v| v.to_string()).collect()))
}

fn existential_spec(i: &str) -> IResult<&str, ExistentialSpec> {
  let (i, name)   = c_id(i)?;
  let (i, _)      = multispace0(i)?;
  let (i, params) = delimited(tag("("),
                              separated_list0(tag(","), parameter),
                              tag(")"))(i)?;
  let (i, _)      = multispace0(i)?;
  let (i, _)      = tag("{")(i)?;
  let (i, _)      = multispace0(i)?;
  let (i, cvars)  = choice_vars(i)?;
  let (i, _)      = multispace0(i)?;
  let (i, pre)    = pre(i)?;
  let (i, _)      = multispace0(i)?;
  let (i, post)   = post(i)?;
  let (i, _)      = multispace0(i)?;
  let (i, _)      = tag("}")(i)?;
  Ok((i, ExistentialSpec {
    name: name.to_string(),
    params,
    choice_vars: cvars,
    pre,
    post,
  }))
}

fn existential_specs(i: &str) -> IResult<&str, Vec<ExistentialSpec>> {
  let (i, _) = label("especs")(i)?;
  many0(existential_spec)(i)
}

fn elaenia_spec(i: &str) -> IResult<&str, ElaeniaSpec> {
  let (i, _)      = multispace0(i)?;
  let (i, _)      = tag("@ELAENIA")(i)?;
  let (i, pre)    = pre(i)?;
  let (i, _)      = multispace0(i)?;
  let (i, afun)   = forall(i)?;
  let (i, _)      = multispace0(i)?;
  let (i, efun)   = exists(i)?;
  let (i, _)      = multispace0(i)?;
  let (i, post)   = post(i)?;
  let (i, _)      = multispace0(i)?;
  let (i, aspecs) = opt(universal_specs)(i)?;
  let (i, _)      = multispace0(i)?;
  let (i, especs) = opt(existential_specs)(i)?;
  let (i, _)      = multispace0(i)?;
  Ok((i, ElaeniaSpec{pre, afun, efun, post,
                     aspecs: aspecs.unwrap_or(Vec::new()),
                     especs: especs.unwrap_or(Vec::new())}))
}

fn parse_elaenia_comment(input: &String) -> Result<ElaeniaSpec, String> {
  let strip_re = Regex::new(r"(?m)\n|^\s*/\*|^\s*\*/|^\s*\*").unwrap();
  let stripped_input = strip_re.replace_all(input, "");
  match elaenia_spec(&stripped_input) {
    Ok((_, result)) => Ok(result),
    Err(e) => Err(e.to_string()),
  }
}

pub fn parse_elaenia_spec(input_file: &String) -> Result<ElaeniaSpec, String> {
  match fs::read_to_string(input_file) {
    Err(err) => Err(err.to_string()),
    Ok(input) => parse_elaenia_comment(&input),
  }
}

#[cfg(test)]
mod test {
  use super::*;

  #[test]
  fn test_elaenia_spec_comment() {
    let input =
      "/* @ELAENIA
        * pre: true;
        * forall: refinement;
        * exists: original;
        * post: original.x == refinement.x;
        * aspecs: refinedRand() {
        *     pre:  true;
        *     post: ret! % 2 == 1;
        * }
        * especs:
        *   originalRand() {
        *     choiceVars: n;
        *     pre:  true;
        *     post: ret! == n;
        * }
        */".to_string();
    let expected = ElaeniaSpec {
      pre: KestrelCond::BExpr(CondBExpr::True),
      afun: "refinement".to_string(),
      efun: "original".to_string(),
      post: KestrelCond::BExpr(CondBExpr::BinopA {
        lhs: CondAExpr::QualifiedVar {
          exec: "original".to_string(),
          name: "x".to_string()
        },
        rhs: CondAExpr::QualifiedVar {
          exec: "refinement".to_string(),
          name: "x".to_string()
        },
        op: CondBBinopA::Eq,
      }),
      aspecs: vec!(UniversalSpec {
        name: "refinedRand".to_string(),
        params: vec!(),
        pre: KestrelCond::BExpr(CondBExpr::True),
        post: KestrelCond::BExpr(CondBExpr::BinopA {
          lhs: CondAExpr::Binop {
            lhs: Box::new(CondAExpr::ReturnValue),
            rhs: Box::new(CondAExpr::Int(2)),
            op: CondABinop::Mod,
          },
          rhs: CondAExpr::Int(1),
          op: CondBBinopA::Eq,
        }),
      }),
      especs: vec!(ExistentialSpec {
        name: "originalRand".to_string(),
        params: vec!(),
        choice_vars: vec!("n".to_string()),
        pre: KestrelCond::BExpr(CondBExpr::True),
        post: KestrelCond::BExpr(CondBExpr::BinopA {
          lhs: CondAExpr::ReturnValue,
          rhs: CondAExpr::Var("n".to_string()),
          op: CondBBinopA::Eq,
        }),
      }),
    };
    let actual = parse_elaenia_comment(&input).unwrap();
    assert_eq!(actual, expected);
  }
}
