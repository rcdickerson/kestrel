use crate::eggroll::ast::*;
use egg::*;

pub fn rewrites(with_loop_sched: bool) -> Vec<Rewrite<Eggroll, ()>> {
  let mut rewrites = vec![
    rewrite!("prod-assoc-l"; "(seq ?a (seq ?b ?c))" => "(seq (seq ?a ?b) ?c)"),
    rewrite!("prod-assoc-r"; "(seq (seq ?a ?b) ?c)" => "(seq ?a (seq ?b ?c))"),
    rewrite!("rel-embed"; "(<|> ?x ?y)" => "(seq (<| ?x) (|> ?y))"),
    rewrite!("embed-comm-l"; "(seq (<| ?x) (|> ?y))" => "(seq (|> ?y) (<| ?x))"),
    rewrite!("embed-comm-r"; "(seq (|> ?y) (<| ?x))" => "(seq (<| ?x) (|> ?y))"),
    rewrite!("rel-unembed"; "(seq (<| ?x) (|> ?y))" => "(<|> ?x ?y)"),
    rewrite!("embed-hom-l"; "(<| (seq ?x ?y))" => "(seq (<| ?x) (<| ?y))"),
    rewrite!("embed-hom-r"; "(|> (seq ?x ?y))" => "(seq (|> ?x) (|> ?y))"),
    rewrite!("while-lockstep"; "(<|> (while ?e1 ?i1 ?c1) (while ?e2 ?i2 ?c2))"
                            => "(while-lockstep 0 0 ?e1 ?e2 ?i1 ?i2 ?c1 ?c2 (<|> ?c1 ?c2))"),
  ];
  if with_loop_sched {
    rewrites.append(&mut vec![
      rewrite!("while-scheduled21"; "(<|> (while ?e1 ?i1 ?c1) (while ?e2 ?i2 ?c2))"
                                 => "(while-scheduled 0 0 2 1 ?e1 ?e2 ?i1 ?i2 ?c1 ?c2)"),
      rewrite!("while-scheduled12"; "(<|> (while ?e1 ?i1 ?c1) (while ?e2 ?i2 ?c2))"
                                 => "(while-scheduled 0 0 1 2 ?e1 ?e2 ?i1 ?i2 ?c1 ?c2)"),

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
    ]);
  }
  rewrites
}
