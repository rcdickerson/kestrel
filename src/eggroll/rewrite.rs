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
    rewrite!("while-align"; "(<|> (while ?e1 ?i1 ?c1) (while ?e2 ?i2 ?c2))"
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
    rewrite!("if-else-skip"; "(if ?c ?t)" => "(if-else ?c ?t skip)"),
    rewrite!("if-align"; "(<|> (if-else ?c1 ?t1 ?e1) (if-else ?c2 ?t2 ?e2))"
                      => "(if-rel ?c1 ?c2 ?t1 ?t2 ?e1 ?e2)"),
    rewrite!("if-rel-expand"; "(if-rel ?c1 ?c2 ?t1 ?t2 ?e1 ?e2)"
             => "(if-else (&& ?c1 ?c2)       (<|> ?t1 ?t2)
                 (if-else (&& ?c1 (not ?c2)) (<|> ?t1 ?e2)
                 (if-else (&& (not ?c1) ?c2) (<|> ?e1 ?t2)
                 (<|> ?e1 ?e2))))"),
    rewrite!("push-rel-if-l"; "(<|> (if-else ?c ?t ?e) ?s)" => "(if-rel ?c (const-int 1) ?t ?s ?e ?s)"),
    rewrite!("push-rel-if-r"; "(<|> ?s (if-else ?c ?t ?e))" => "(if-rel (const-int 1) ?c ?s ?t ?s ?e)"),

    // rewrite!("if-align"; "(<|> (if-else ?c1 ?t1 ?e1) (if-else ?c2 ?t2 ?e2))"
    //                   => "(if-rel ?c1 ?c2 (<|> ?t1 ?t2) (<|> ?e1 ?e2))"),
    // rewrite!("push-rel-if-l"; "(<|> (if-else ?c ?t ?e) ?s)" => "(if-rel ?c true (<|> ?t ?s) (<|> ?e ?s))"),
    // rewrite!("push-rel-if-r"; "(<|> ?s (if-else ?c ?t ?e))" => "(if-rel true ?c (<|> ?s ?t) (<|> ?s ?e))"),
  ]
}

#[derive(Hash, Debug)]
struct UnrollWhile {
  cond: Var,
  inv: Var,
  body: Var,
}
impl Applier<Eggroll, ()> for UnrollWhile {
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
