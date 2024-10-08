use std::hash::{DefaultHasher, Hash, Hasher};

use crate::eggroll::ast::*;
use egg::*;

pub fn rewrites() -> Vec<Rewrite<Eggroll, ()>> {
  vec![
    rewrite!("prod-assoc-l"; "(seq ?a (seq ?b ?c))" => "(seq (seq ?a ?b) ?c)"),
    rewrite!("prod-assoc-r"; "(seq (seq ?a ?b) ?c)" => "(seq ?a (seq ?b ?c))"),
    rewrite!("seq-repeat-collapse"; "(seq (guarded-repeat ?i ?e ?c) (guarded-repeat ?i ?e ?c))"
                                 => "(guarded-repeat ?i ?e ?c)"),
    rewrite!("rel-embed"; "(<|> ?x ?y)" => "(seq (<| ?x) (|> ?y))"),
    rewrite!("embed-comm-l"; "(seq (<| ?x) (|> ?y))" => "(seq (|> ?y) (<| ?x))"),
    rewrite!("embed-comm-r"; "(seq (|> ?y) (<| ?x))" => "(seq (<| ?x) (|> ?y))"),
    rewrite!("rel-unembed"; "(seq (<| ?x) (|> ?y))" => "(<|> ?x ?y)"),
    rewrite!("embed-hom-l"; "(<| (seq ?x ?y))" => "(seq (<| ?x) (<| ?y))"),
    rewrite!("embed-hom-r"; "(|> (seq ?x ?y))" => "(seq (|> ?x) (|> ?y))"),
    rewrite!("while-r"; "(<|> (while ?e1 ?i1 ?c1) (while ?e2 ?i2 ?c2))"
                       => "(while-rel ?e1 ?e2 ?i1 ?i2 ?c1 ?c2)"),
    rewrite!("while-sched"; "(while-rel ?e1 ?e2 ?i1 ?i2 ?c1 ?c2)"
             => { ScheduleWhile {
                    cond1: "?e1".parse().unwrap(),
                    cond2: "?e2".parse().unwrap(),
                    inv1: "?i1".parse().unwrap(),
                    inv2: "?i2".parse().unwrap(),
                    body1: "?c1".parse().unwrap(),
                    body2: "?c2".parse().unwrap(),
                }}),
    rewrite!("while-unroll"; "(while ?e ?i ?c)"
             => { UnrollWhile {
                    cond: "?e".parse().unwrap(),
                    inv: "?i".parse().unwrap(),
                    body: "?c".parse().unwrap(),
                 }}),
    rewrite!("push-rel-if-l"; "(<|> (if ?c ?t) ?s)" => "(if-else ?c (<|> ?t ?s) ?s)"),
    rewrite!("push-rel-if-else-l"; "(<|> (if-else ?c ?t ?e) ?s)" => "(if-else ?c (<|> ?t ?s) (<|> ?e ?s))"),
    rewrite!("push-rel-if-r"; "(<|> ?s (if ?c ?t))" => "(if-else ?c (<|> ?s ?t) ?s)"),
    rewrite!("push-rel-if-else-r"; "(<|> ?s (if-else ?c ?t ?e))" => "(if-else ?c (<|> ?s ?t) (<|> ?s ?e))"),
  ]
}

#[derive(Hash, Debug)]
struct UnrollWhile {
  cond: Var,
  inv: Var,
  body: Var,
}
impl UnrollWhile {
  pub fn already_unrolled(&self, egraph: &mut EGraph<Eggroll, ()>, matched_id: Id) -> bool {
    for sibling in &egraph[matched_id].nodes {
      match sibling {
        Eggroll::Seq(children) => {
          for left_child in &egraph[children[0]].nodes {
            match left_child {
              Eggroll::GuardedRepeat(_) => return true,
              _ => (),
            }
          }
        },
        _ => (),
      }
    }
    false
  }
}
impl Applier<Eggroll, ()> for UnrollWhile {
  fn apply_one(&self,
               egraph: &mut EGraph<Eggroll, ()>,
               matched_id: Id,
               subst: &Subst,
               _: Option<&PatternAst<Eggroll>>,
               _: Symbol) -> Vec<Id> {
//    if self.already_unrolled(egraph, matched_id) {
//      return vec![]
//    }
    let hasher = &mut DefaultHasher::new();
    self.hash(hasher);
    let id = format!("id{}", hasher.finish()).to_string();
    let rep_id = egraph.add(Eggroll::RawString(id));
    let repeat = egraph.add(Eggroll::GuardedRepeat([rep_id, subst[self.cond], subst[self.body]]));
    let while_loop = egraph.add(Eggroll::While(
      [subst[self.cond], subst[self.inv], subst[self.body]]));
    let seq = egraph.add(Eggroll::Seq([repeat, while_loop]));
    if egraph.union(matched_id, seq) {
      vec![seq]
    } else {
      vec![]
    }
  }
}

#[derive(Hash, Debug)]
struct ScheduleWhile {
  cond1: Var,
  cond2: Var,
  inv1: Var,
  inv2: Var,
  body1: Var,
  body2: Var,
}
impl Applier<Eggroll, ()> for ScheduleWhile {
  fn apply_one(&self,
               egraph: &mut EGraph<Eggroll, ()>,
               matched_id: Id,
               subst: &Subst,
               _: Option<&PatternAst<Eggroll>>,
               _: Symbol) -> Vec<Id> {
    let hasher = &mut DefaultHasher::new();
    self.hash(hasher);
    let id = format!("id{}", hasher.finish()).to_string();
    let rep_id = egraph.add(Eggroll::RawString(id));
    let rep_while = egraph.add(Eggroll::GuardedRepeatWhile(
      [rep_id,
       subst[self.cond1], subst[self.cond2],
       subst[self.inv1], subst[self.inv2],
       subst[self.body1], subst[self.body2]]));
    if egraph.union(matched_id, rep_while) {
      vec![rep_while]
    } else {
      vec![]
    }
  }
}

fn disjoint(vars: Vec<&'static str>)
            -> impl Fn(&mut EGraph<Eggroll, ()>, Id, &Subst)
            -> bool {
  let vars = vars.into_iter().map(|var| var.parse().unwrap()).collect::<Vec<_>>();
  move |egraph, _, subst| {
    for a in &vars {
      for b in &vars {
        if a == b { continue; }
        if egraph[subst[*a]].id == egraph[subst[*b]].id {
          return false
        }
      }
    }
    return true
  }
}

fn ok_seq(a: &'static str, b: &'static str, c: &'static str)
            -> impl Fn(&mut EGraph<Eggroll, ()>, Id, &Subst)
            -> bool {
  let a = a.parse().unwrap();
  let b = b.parse().unwrap();
  let c = c.parse().unwrap();
  move |egraph, match_id, subst| {
    egraph[subst[a]].id != match_id && egraph[subst[b]].id != match_id && egraph[subst[c]].id != match_id
  }
}
