use std::hash::{DefaultHasher, Hash, Hasher};

use crate::eggroll::ast::*;
use egg::*;

pub fn rewrites() -> Vec<Rewrite<Eggroll, ()>> {
  vec![
    rewrite!("prod-assoc-l"; "(seq ?a (seq ?b ?c))" => "(seq (seq ?a ?b) ?c)"),
    rewrite!("prod-assoc-r"; "(seq (seq ?a ?b) ?c)" => "(seq ?a (seq ?b ?c))"),
    rewrite!("rel-embed"; "(<|> ?x ?y)" => "(seq (<| ?x) (|> ?y))"),
    rewrite!("embed-comm-l"; "(seq (<| ?x) (|> ?y))" => "(seq (|> ?y) (<| ?x))"),
    rewrite!("embed-comm-r"; "(seq (|> ?y) (<| ?x))" => "(seq (<| ?x) (|> ?y))"),
    rewrite!("rel-unembed"; "(seq (<| ?x) (|> ?y))" => "(<|> ?x ?y)"),
    rewrite!("embed-hom-l"; "(<| (seq ?x ?y))" => "(seq (<| ?x) (<| ?y))"),
    rewrite!("embed-hom-r"; "(|> (seq ?x ?y))" => "(seq (|> ?x) (|> ?y))"),
    rewrite!("while-r"; "(<|> (while ?e1 ?i1 ?c1) (while ?e2 ?i2 ?c2))"
                       => "(while-rel ?e1 ?e2 ?i1 ?i2 ?c1 ?c2)"),
    rewrite!("while-sched"; "(while-rel ?e1 ?e2 ?i1 ?i2 ?c1 ?c2)"
             => { GuardedRepeatWhile {
                  cond1: "?e1".parse().unwrap(),
                  cond2: "?e2".parse().unwrap(),
                  inv1: "?i1".parse().unwrap(),
                  inv2: "?i2".parse().unwrap(),
                  body1: "?c1".parse().unwrap(),
                  body2: "?c2".parse().unwrap(),
                }}),
//    rewrite!("while-unroll"; "(while ?e ?i ?c)" => "(seq (guarded-repeat ?e ?c) (while ?e ?i ?c))"),
    rewrite!("push-rel-if-l"; "(<|> (if ?c ?t) ?s)" => "(if-else ?c (<|> ?t ?s) ?s)"),
    rewrite!("push-rel-if-else-l"; "(<|> (if-else ?c ?t ?e) ?s)" => "(if-else ?c (<|> ?t ?s) (<|> ?e ?s))"),
    rewrite!("push-rel-if-r"; "(<|> ?s (if ?c ?t))" => "(if-else ?c (<|> ?s ?t) ?s)"),
    rewrite!("push-rel-if-else-r"; "(<|> ?s (if-else ?c ?t ?e))" => "(if-else ?c (<|> ?s ?t) (<|> ?s ?e))"),
  ]

//  rewrites.append(&mut vec![
//      rewrite!("unroll-while"; "(while ?e ?i ?c)" => "(seq (if ?e ?c) (while ?e ?i ?c))"),
//      rewrite!("while-scheduled21"; "(<|> (while ?e1 ?i1 ?c1) (while ?e2 ?i2 ?c2))"
//                                 => "(while-scheduled 0 0 2 1 ?e1 ?e2 ?i1 ?i2 ?c1 ?c2)"),
//      rewrite!("while-scheduled12"; "(<|> (while ?e1 ?i1 ?c1) (while ?e2 ?i2 ?c2))"
//                                 => "(while-scheduled 0 0 1 2 ?e1 ?e2 ?i1 ?i2 ?c1 ?c2)"),

/*
      rewrite!("unroll-lock-l01"; "(while-lockstep 0 0 ?e1 ?e2 ?i1 ?i2 ?c1 ?c2 ?body)"
                               => "(while-lockstep 1 0 ?e1 ?e2 ?i1 ?i2 ?c1 ?c2 ?body)"),
      rewrite!("unroll-lock-l12"; "(while-lockstep 1 0 ?e1 ?e2 ?i1 ?i2 ?c1 ?c2 ?body)"
                               => "(while-lockstep 2 0 ?e1 ?e2 ?i1 ?i2 ?c1 ?c2 ?body)"),
      rewrite!("unroll-lock-r01"; "(while-lockstep 0 0 ?e1 ?e2 ?i1 ?i2 ?c1 ?c2 ?body)"
                               => "(while-lockstep 0 1 ?e1 ?e2 ?i1 ?i2 ?c1 ?c2 ?body)"),
      rewrite!("unroll-lock-r12"; "(while-lockstep 0 1 ?e1 ?e2 ?i1 ?i2 ?c1 ?c2 ?body)"
                               => "(while-lockstep 0 2 ?e1 ?e2 ?i1 ?i2 ?c1 ?c2 ?body)"),

      rewrite!("unroll-sched-l01"; "(while-scheduled 0 0 ?sl ?sr ?e1 ?e2 ?i1 ?i2 ?c1 ?c2)"
                                => "(while-scheduled 1 0 ?sl ?sr ?e1 ?e2 ?i1 ?i2 ?c1 ?c2)"),
      rewrite!("unroll-sched-l12"; "(while-scheduled 1 0 ?sl ?sr ?e1 ?e2 ?i1 ?i2 ?c1 ?c2)"
                                => "(while-scheduled 2 0 ?sl ?sr ?e1 ?e2 ?i1 ?i2 ?c1 ?c2)"),
      rewrite!("unroll-sched-r01"; "(while-scheduled 0 0 ?sl ?sr ?e1 ?e2 ?i1 ?i2 ?c1 ?c2)"
                                => "(while-scheduled 0 1 ?sl ?sr ?e1 ?e2 ?i1 ?i2 ?c1 ?c2)"),
      rewrite!("unroll-sched-r12"; "(while-scheduled 0 1 ?sl ?sr ?e1 ?e2 ?i1 ?i2 ?c1 ?c2)"
                                => "(while-scheduled 0 2 ?sl ?sr ?e1 ?e2 ?i1 ?i2 ?c1 ?c2)"),

      rewrite!("rev-while-scheduled21"; "(while-scheduled ?ul ?ur 2 1 ?e1 ?e2 ?i1 ?i2 ?c1 ?c2)"
                                     => "(<|> (while ?e1 ?i1 ?c1) (while ?e2 ?i2 ?c2))"),
      rewrite!("rev-while-scheduled12"; "(while-scheduled ?ul ?ur 1 2 ?e1 ?e2 ?i1 ?i2 ?c1 ?c2)"
                                     => "(<|> (while ?e1 ?i1 ?c1) (while ?e2 ?i2 ?c2))"),
      rewrite!("rev-while-lockstep"; "(while-lockstep 0 0 ?e1 ?e2 ?i1 ?i2 ?c1 ?c2 (<|> ?c1 ?c2))"
                                  => "(<|> (while ?e1 ?i1 ?c1) (while ?e2 ?i2 ?c2))"),
*/
//  ]);
}

#[derive(Hash, Debug)]
struct GuardedRepeatWhile {
  cond1: Var,
  cond2: Var,
  inv1: Var,
  inv2: Var,
  body1: Var,
  body2: Var,
}
impl Applier<Eggroll, ()> for GuardedRepeatWhile {
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
