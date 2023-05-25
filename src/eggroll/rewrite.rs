use crate::eggroll::ast::*;
use egg::*;

pub fn make_rules() -> Vec<Rewrite<Eggroll, ()>> {
  vec![
    rewrite!("prod-assoc-l"; "(seq ?a (seq ?b ?c))" => "(seq (seq ?a ?b) ?c)"),
    rewrite!("prod-assoc-r"; "(seq (seq ?a ?b) ?c)" => "(seq ?a (seq ?b ?c))"),
    rewrite!("rel-embed"; "(<|> ?x ?y)" => "(seq (<| ?x) (|> ?y))"),
    rewrite!("embed-comm-l"; "(seq (<| ?x) (|> ?y))" => "(seq (|> ?y) (<| ?x))"),
    rewrite!("embed-comm-r"; "(seq (|> ?y) (<| ?x))" => "(seq (<| ?x) (|> ?y))"),
    rewrite!("rel-unembed"; "(seq (<| ?x) (|> ?y))" => "(<|> ?x ?y)"),
    rewrite!("embed-hom-l"; "(<| (seq ?x ?y))" => "(seq (<| ?x) (<| ?y))"),
    rewrite!("embed-hom-r"; "(|> (seq ?x ?y))" => "(seq (|> ?x) (|> ?y))"),
    rewrite!("while-lockstep11"; "(<|> (while ?e1 ?c1) (while ?e2 ?c2))" =>
                                 "(while-lockstep 1 1 ?e1 ?e2 ?c1 ?c2)"),
    rewrite!("while-lockstep21"; "(<|> (while ?e1 ?c1) (while ?e2 ?c2))" =>
                                 "(while-lockstep 2 1 ?e1 ?e2 ?c1 ?c2)"),
    rewrite!("while-lockstep12"; "(<|> (while ?e1 ?c1) (while ?e2 ?c2))" =>
                                 "(while-lockstep 1 2 ?e1 ?e2 ?c1 ?c2)"),
  ]
}
