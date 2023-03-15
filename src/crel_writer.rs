use crate::crel::*;

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
