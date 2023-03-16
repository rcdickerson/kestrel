use crate::crel::ast::*;
use sexp::{Atom, Sexp};

impl CRel {
  pub fn to_c(&self) -> String {
    crel_to_c(self)
  }
}

pub fn crel_to_c(crel: &CRel) -> String {
  match crel {
    CRel::Add(lhs, rhs) => {
      format!("{} + {}", crel_to_c(lhs), crel_to_c(rhs))
    }
    CRel::Asgn{lhs, rhs} => format!("{} = {}", crel_to_c(lhs), crel_to_c(rhs)),
    CRel::Call{callee, args} => {
      let args_c = args.iter().map(crel_to_c).collect::<Vec<String>>().join(", ");
      format!("{}({})", callee, args_c)
    }
    CRel::ConstInt(i) => i.to_string(),
    CRel::Declaration{specifiers, declarators} => {
      let spec_c = specifiers.iter().map(crel_specifier_to_c).collect::<Vec<String>>().join(" ");
      let dec_c = declarators.iter().map(crel_to_c).collect::<Vec<String>>().join(" ");
      format!("{} {}", spec_c, dec_c)
    },
    CRel::Eq(lhs, rhs) => {
      format!("{} == {}", crel_to_c(lhs), crel_to_c(rhs))
    }
    CRel::FunDef{specifiers, name, args, body} => {
      let spec_c= specifiers.iter().map(crel_specifier_to_c).collect::<Vec<String>>().join(" ");
      let args_c = args.iter().map(crel_to_c).collect::<Vec<String>>().join(", ");
      let body_c = crel_to_c(body);
      format!("{} {}({}) {{\n{}\n}}", spec_c, name, args_c, body_c)
    }
    CRel::Id(name) => name.clone(),
    CRel::Init{var, val} => {
      match val {
        None => crel_to_c(var),
        Some(v) => format!("{} = {}", crel_to_c(var), crel_to_c(v)),
      }
    }
    CRel::Lte(lhs, rhs) => {
      format!("{} <= {}", crel_to_c(lhs), crel_to_c(rhs))
    }
    CRel::Rel{lhs, rhs} => {
      // Concatenate relations.
      format!("{}\n{}", crel_to_c(lhs), crel_to_c(rhs))
    }
    CRel::Return(crel) => format!("return {}", crel_to_c(crel)),
    CRel::Seq(crels) => {
      let seq_c = crels.iter()
        .map(crel_to_c)
        .collect::<Vec<String>>()
        .join(";\n");
      format!("{};", seq_c)
    }
    CRel::While{cond, body} => format!("while ({}) {{\n{}\n}}",
                                       crel_to_c(cond),
                                       crel_to_c(body)),
    _ => "".to_string(),
  }
}

fn crel_specifier_to_c(crel_spec: &CRelSpecifier) -> String {
  match crel_spec {
    CRelSpecifier::TypeSpecifier(ty) => match ty {
      CRelType::Float => "float".to_string(),
      CRelType::Int   => "int".to_string(),
      CRelType::Void  => "void".to_string(),
      _ => "".to_string(),
    }
    _ => "".to_string(),
  }
}

pub fn crel_to_egg(crel: &CRel) -> String {
  match crel {
    CRel::Add(lhs, rhs) => {
      format!("(+ {} {})", crel_to_egg(lhs), crel_to_egg(rhs))
    }
    CRel::Asgn{lhs, rhs} => format!("(:= {} {})", crel_to_egg(lhs), crel_to_egg(rhs)),
    CRel::Call{callee, args} => {
      let args_egg = args.iter().map(crel_to_c).collect::<Vec<String>>().join(" ");
      format!("(call {} {})", callee, args_egg)
    }
    CRel::ConstInt(i) => i.to_string(),
    CRel::Declaration{specifiers, declarators} => {
      let spec_egg = specifiers.iter().map(crel_specifier_to_egg).collect::<Vec<String>>().join(" ");
      let dec_egg = declarators.iter().map(crel_to_egg).collect::<Vec<String>>().join(" ");
      format!("(declaration (specifiers {}) (declarators {}))", spec_egg, dec_egg)
    },
    CRel::Eq(lhs, rhs) => {
      format!("(== {} {})", crel_to_egg(lhs), crel_to_egg(rhs))
    }
    CRel::FunDef{specifiers, name, args, body} => {
      let spec_egg= specifiers.iter().map(crel_specifier_to_egg).collect::<Vec<String>>().join(" ");
      let args_egg = args.iter().map(crel_to_egg).collect::<Vec<String>>().join(" ");
      let body_egg = crel_to_egg(body);
      format!("(fundef {} (specifiers {}) (args {}) {})", name, spec_egg, args_egg, body_egg)
    }
    CRel::Id(name) => name.clone(),
    CRel::Init{var, val} => {
      match val {
        None => crel_to_egg(var),
        Some(v) => format!("(:= {} {})", crel_to_egg(var), crel_to_egg(v)),
      }
    }
    CRel::Lte(lhs, rhs) => {
      format!("(<= {} {})", crel_to_egg(lhs), crel_to_egg(rhs))
    }
    CRel::Rel{lhs, rhs} => {
      format!("(<|> {} {})", crel_to_egg(lhs), crel_to_egg(rhs))
    }
    CRel::Return(crel) => format!("(return {})", crel_to_egg(crel)),
    CRel::Seq(crels) => {
      match crels.len() {
        0 => "".to_string(),
        1 => crel_to_egg(&crels[0]),
        _ => format!("(seq {} {})",
                     crel_to_egg(&crels[0]),
                     crel_to_egg(&CRel::Seq(crels[1..].to_vec())))
      }
    }
    CRel::While{cond, body} => format!("(while {} {})", crel_to_egg(cond), crel_to_egg(body)),
    _ => "".to_string(),
  }
}

fn crel_specifier_to_egg(crel_spec: &CRelSpecifier) -> String {
  match crel_spec {
    CRelSpecifier::TypeSpecifier(ty) => match ty {
      CRelType::Float => "float".to_string(),
      CRelType::Int   => "int".to_string(),
      CRelType::Void  => "void".to_string(),
      _ => "".to_string(),
    }
    _ => "".to_string(),
  }
}

pub fn egg_to_crel(egg: &String) -> CRel {
  match sexp::parse(egg.as_str()) {
    Err(msg) => panic!("{}", msg),
    Ok(sexp) => egg_sexp_to_crel(&sexp),
  }
}

fn egg_sexp_to_crel(sexp: &Sexp) -> CRel {
  match &sexp {
    Sexp::Atom(atom) => match atom {
      Atom::S(s) => CRel::Id(s.clone()),
      Atom::I(i) => CRel::ConstInt(i32::try_from(i.clone()).unwrap()),
      Atom::F(_) => panic!("Floats currently unsupported"),
    }
    Sexp::List(sexps) => match &sexps[0] {
      Sexp::Atom(Atom::S(s)) if s.as_str() == "+" => {
        let lhs = egg_sexp_to_crel(&sexps[1]);
        let rhs = egg_sexp_to_crel(&sexps[2]);
        CRel::Add(Box::new(lhs), Box::new(rhs))
      },
      Sexp::Atom(Atom::S(s)) if s.as_str() == "declaration" => {
        let specifiers  = egg_sexp_to_crel_specifiers(&sexps[1]);
        let declarators = expect_list_with_head("declarators", &sexps[2]);
        CRel::Declaration{specifiers, declarators}
      },
      Sexp::Atom(Atom::S(s)) if s.as_str() == "fundef" => {
        let name = expect_str(&sexps[1]);
        let specifiers = egg_sexp_to_crel_specifiers(&sexps[2]);
        let args = match &sexps[3] {
          Sexp::Atom(_) => Vec::new(),
          Sexp::List(args) => args.iter().map(egg_sexp_to_crel).collect(),
        };
        let body = egg_sexp_to_crel(&sexps[4]);
        CRel::FunDef{specifiers, name, args, body: Box::new(body)}
      },
      Sexp::Atom(Atom::S(s)) if s.as_str() == "seq" => {
        let lhs = egg_sexp_to_crel(&sexps[1]);
        let rhs = egg_sexp_to_crel(&sexps[2]);
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
        list[1..].iter().map(egg_sexp_to_crel).collect()
    },
    _ => panic!("Expected head of list to be {}", head)
  }
}

fn egg_sexp_to_crel_specifiers(sexp: &Sexp) -> Vec<CRelSpecifier> {
  match &sexp {
    Sexp::Atom(_) => Vec::new(),
    Sexp::List(specs) if specs.len() < 2 => Vec::new(),
    Sexp::List(specs) => specs[1..].iter().map(egg_sexp_to_crel_specifier).collect(),
  }
}

fn egg_sexp_to_crel_specifier(sexp: &Sexp) -> CRelSpecifier {
  match &sexp {
    Sexp::Atom(Atom::S(s)) if s.as_str() == "int" => CRelSpecifier::TypeSpecifier(CRelType::Int),
    _ => CRelSpecifier::Uninterp(sexp.to_string())
  }
}
