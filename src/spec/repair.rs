// Automatic specification repair
use crate::spec::KestrelSpec;
use crate::crel::unaligned::UnalignedCRel;
use crate::spec::condition::*;
use crate::crel::ast::TypeName;
use std::collections::HashMap;

struct PostConditionPair {
    left_var_name: String,
    right_var_name: String,
    comparison: CondBBinopA,
    left_type: Option<TypeName>,
    right_type: Option<TypeName>,
    changed: bool,
}

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

// So we are searching for "(int)(*((unsigned int*)(& "
// which is the type of r_ret_val cast as the type of l_ret_val. 

pub fn repair_spec(spec: &KestrelSpec, unaligned: &UnalignedCRel) -> KestrelSpec {
    let mut pairs = build_post_condition_pairs(spec);
    let (left_vars, right_vars) = build_variable_maps(unaligned);
    resolve_types(&mut pairs, &left_vars, &right_vars);
    apply_repairs(spec, &pairs)
}

fn build_post_condition_pairs(spec: &KestrelSpec) -> Vec<PostConditionPair> {
    Vec::new()
}

fn build_variable_maps(unaligned: &UnalignedCRel) -> 
(HashMap<String, TypeName>, HashMap<String, TypeName>) {
    (HashMap::new(), HashMap::new())
}

fn resolve_types(pairs: &mut Vec<PostConditionPair>, 
    left_vars: &HashMap<String, TypeName>, right_vars: &HashMap<String, TypeName>) {
    // Code that resolves types here
}

fn apply_repairs(spec: &KestrelSpec, pairs: &Vec<PostConditionPair>) -> KestrelSpec {
    spec.clone()
}