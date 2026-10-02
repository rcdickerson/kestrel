// Abduces a mapping from postcondition variables to the program
// variables that represent them, checked against execution traces.

use crate::crel::ast::TypeName;
use crate::crel::unaligned::UnalignedCRel;
use crate::names::CollectVarTypes;
use crate::spec::KestrelSpec;
use crate::spec::condition::CondAExpr;
use std::collections::{HashMap, HashSet};
use std::path::Path;

// Reference Spec File (Simple)
/* @KESTREL
 * pre: left.x == right.x;
 * left: left;
 * right: right;
 * NEEDED post: left.ret_val == (int)(*((unsigned int*)(&right.ret_val)));
 * GIVEN post: left.ret_val == right.ret_val;
 */

// Reference unaligned code (Simple)
//  void main(int l_x, int r_x) {
//   int l_ret_val = (l_x + 1);
//   char r_ret_val[4];
//   char r_x_var1[4];
//   (*((unsigned int*)(&r_x_var1))) = r_x;
//   (*((unsigned int*)(&r_ret_val))) = (r_x + 1);
// }

// dtrace_path is an Option until the trace file handoff is worked out.
pub fn abduce_var_mapping(spec: &KestrelSpec, unaligned_crel: &UnalignedCRel, dtrace_path: Option<&Path>) -> KestrelSpec {
    let prog_vars = unaligned_crel.unaligned_main.var_types();
    let post_vars = spec.post.state_vars();
    let mapping = perform_abduction(spec, &prog_vars, &post_vars, dtrace_path);
    apply_mapping(spec, &mapping)
}

fn perform_abduction(spec: &KestrelSpec,
                     prog_vars: &HashMap<String, TypeName>,
                     post_vars: &HashSet<String>,
                     dtrace_path: Option<&Path>) -> HashMap<String, CondAExpr> {
    // Goal: find each postcondition variable's real equivalent in the code.
    HashMap::new()
}

fn apply_mapping(spec: &KestrelSpec, mapping: &HashMap<String, CondAExpr>) -> KestrelSpec {
    spec.clone()
}
