use crate::crel::ast::*;
use sexp::{Atom, Sexp};

pub fn eggroll_to_crel(egg: &String) -> CRel {
  match sexp::parse(egg.as_str()) {
    Err(msg) => panic!("{}", msg),
    Ok(sexp) => eggroll_sexp_to_crel(&sexp),
  }
}

fn eggroll_sexp_to_crel(sexp: &Sexp) -> CRel {
  match &sexp {
    Sexp::Atom(atom) => match atom {
      Atom::S(s) => CRel::Id(s.clone()),
      Atom::I(i) => CRel::ConstInt(i32::try_from(i.clone()).unwrap()),
      Atom::F(_) => panic!("Floats currently unsupported"),
    }
    Sexp::List(sexps) => match &sexps[0] {
      Sexp::Atom(Atom::S(s)) if s.as_str() == "+" => {
        let lhs = eggroll_sexp_to_crel(&sexps[1]);
        let rhs = eggroll_sexp_to_crel(&sexps[2]);
        CRel::Add(Box::new(lhs), Box::new(rhs))
      },
      Sexp::Atom(Atom::S(s)) if s.as_str() == "declaration" => {
        let specifiers  = eggroll_sexp_to_crel_specifiers(&sexps[1]);
        let declarators = expect_list_with_head("declarators", &sexps[2]);
        CRel::Declaration{specifiers, declarators}
      },
      Sexp::Atom(Atom::S(s)) if s.as_str() == "fundef" => {
        let name = expect_str(&sexps[1]);
        let specifiers = eggroll_sexp_to_crel_specifiers(&sexps[2]);
        let args = match &sexps[3] {
          Sexp::Atom(_) => Vec::new(),
          Sexp::List(args) => args.iter().map(eggroll_sexp_to_crel).collect(),
        };
        let body = eggroll_sexp_to_crel(&sexps[4]);
        CRel::FunDef{specifiers, name, args, body: Box::new(body)}
      },
      Sexp::Atom(Atom::S(s)) if s.as_str() == "seq" => {
        let lhs = eggroll_sexp_to_crel(&sexps[1]);
        let rhs = eggroll_sexp_to_crel(&sexps[2]);
        CRel::Seq(vec!(lhs, rhs))
      }
      _ => CRel::Uninterp(format!("{:?}", sexps))
    }
  }
}

fn expect_list(sexp: &Sexp) -> Vec<Sexp> {
  match sexp {
    Sexp::List(lst) => lst.clone(),
    _ => panic!("Expected list"),
  }
}

fn expect_str(sexp: &Sexp) -> String {
  match sexp {
    Sexp::Atom(Atom::S(s)) => s.clone(),
    _ => panic!("Expected string atom"),
  }
}

fn expect_list_with_head(head: &str, sexp: &Sexp) -> Vec<CRel> {
  let list = expect_list(&sexp);
  if list.is_empty() {
    panic!("Expected non-empty list");
  }
  match &list[0] {
    Sexp::Atom(Atom::S(s)) if s.as_str() == head => {
        list[1..].iter().map(eggroll_sexp_to_crel).collect()
    },
    _ => panic!("Expected head of list to be {}", head)
  }
}

fn eggroll_sexp_to_crel_specifiers(sexp: &Sexp) -> Vec<CRelSpecifier> {
  match &sexp {
    Sexp::Atom(_) => Vec::new(),
    Sexp::List(specs) if specs.len() < 2 => Vec::new(),
    Sexp::List(specs) => specs[1..].iter().map(eggroll_sexp_to_crel_specifier).collect(),
  }
}

fn eggroll_sexp_to_crel_specifier(sexp: &Sexp) -> CRelSpecifier {
  match &sexp {
    Sexp::Atom(Atom::S(s)) if s.as_str() == "int" => CRelSpecifier::TypeSpecifier(CRelType::Int),
    _ => CRelSpecifier::Uninterp(sexp.to_string())
  }
}
