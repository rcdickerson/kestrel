// Goal: Abduces a mapping from postcondition variables to the program
// variables that represent them, checked against execution traces.
// Current: Heiistically produce a mapping from post condition variables to the 
// program variables that represent them using accessed types.
// Taking the first type if multiple OR if none taking the original type.

use crate::crel::ast::TypeName;
use crate::crel::unaligned::UnalignedCRel;
use crate::names::{CollectVarTypes, CollectVarAccessTypes};
use crate::spec::KestrelSpec;
use crate::spec::condition::{CondAExpr, CondAUnop, CondBExpr, KestrelCond, qualified_state_var};
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

// GIVEN post as parsed (spec.post):
//   BExpr(BinopA {
//     lhs: QualifiedVar { exec: "left",  name: "ret_val" },
//     rhs: QualifiedVar { exec: "right", name: "ret_val" },
//     op: Eq })

// Unaligned code as CRel:
//   FunctionDefinition "main"
//     params: [Int] l_x, [Unsigned, Int] r_x
//     body: Relation
//       lhs: Declaration [Int]  l_ret_val = l_x + 1
//       rhs: Declaration [Char] Array { name: r_ret_val, sizes: [4] }
//            Declaration [Char] Array { name: r_x_var1,  sizes: [4] }
//            Assign Deref(Cast(Pointer(Base[Unsigned, Int]), Address(r_x_var1)))  = r_x
//            Assign Deref(Cast(Pointer(Base[Unsigned, Int]), Address(r_ret_val))) = r_x + 1

// Walking the example through each step:

// Step 1, prog_vars (unaligned_crel.unaligned_main.var_types()):
//   l_ret_val => Base([Int])
//   l_x       => Base([Int])
//   r_ret_val => Array(Base([Char]), 4)
//   r_x       => Base([Unsigned, Int])
//   r_x_var1  => Array(Base([Char]), 4)

// Step 2, access_types (unaligned_crel.unaligned_main.var_access_types()):
//   r_ret_val => [Base([Unsigned, Int])]
//   r_x_var1  => [Base([Unsigned, Int])]

// Step 3, post_vars (spec.post.state_vars()):
//   {"l_ret_val", "r_ret_val"}

// Step 4, mapping (perform_abduction):
//   l_ret_val has no access types, so it's left alone.
//   r_ret_val has one: r_ret_val => *((unsigned int*)(&r_ret_val))

// Step 5, new post (apply_mapping):
//   l_ret_val == (*((unsigned int*)(&r_ret_val)))
//   That's the needed post.

// Next: find examples the heuristic can't settle before doing the dtrace work.
// For those, the dtrace checks each candidate type. If none fit, we abduce
// one: build up candidate casts, simplest first, until one holds on every run.

// dtrace_path is an Option until the trace file handoff is worked out.
pub fn abduce_var_mapping(spec: &KestrelSpec, unaligned_crel: &UnalignedCRel, dtrace_path: Option<&Path>) -> KestrelSpec {
    let prog_vars = unaligned_crel.unaligned_main.var_types();
    let access_types = unaligned_crel.unaligned_main.var_access_types();
    let post_vars = spec.post.state_vars();
    let mapping = perform_abduction(spec, &prog_vars, &access_types, &post_vars, dtrace_path);
    KestrelSpec { post: apply_mapping(&spec.post, &mapping), ..spec.clone() }
}

fn perform_abduction(spec: &KestrelSpec,
                     prog_vars: &HashMap<String, TypeName>,
                     access_types: &HashMap<String, Vec<TypeName>>,
                     post_vars: &HashSet<String>,
                     dtrace_path: Option<&Path>) -> HashMap<String, CondAExpr> {
    let mut mapping = HashMap::new();
    for post_var in post_vars {
        let types = access_types.get(post_var).cloned().unwrap_or_default();
        match types.len() {
            0 => {},
            _ => { mapping.insert(post_var.clone(), punned_read(post_var, &types[0])); },
        }
    }
     // TODO settle ambiguous cases with the dtrace (instead of taking types[0]), 
     // and abduce when nothing fits.
    mapping
}

// Builds *((T*)(&var))
fn punned_read(var: &String, ty: &TypeName) -> CondAExpr {
    CondAExpr::Unop {
        op: CondAUnop::Deref,
        aexp: Box::new(CondAExpr::Cast {
            ty: TypeName::Pointer(Box::new(ty.clone())),
            aexp: Box::new(CondAExpr::Unop {
                op: CondAUnop::Address,
                aexp: Box::new(CondAExpr::Var(var.clone())),
            }),
        }),
    }
}

// Rebuilds the condition, swapping each mapped variable for its expression.
fn apply_mapping(cond: &KestrelCond, mapping: &HashMap<String, CondAExpr>) -> KestrelCond {
    match cond {
        KestrelCond::BExpr(bexpr) => KestrelCond::BExpr(map_bexpr(bexpr, mapping)),
        KestrelCond::ForLoop{index_var, start, end, body} => KestrelCond::ForLoop {
            index_var: index_var.clone(),
            start: map_aexpr(start, mapping),
            end: map_aexpr(end, mapping),
            body: Box::new(apply_mapping(body, mapping)),
        },
        KestrelCond::And{lhs, rhs} => KestrelCond::And {
            lhs: Box::new(apply_mapping(lhs, mapping)),
            rhs: Box::new(apply_mapping(rhs, mapping)),
        },
    }
}

fn map_bexpr(bexpr: &CondBExpr, mapping: &HashMap<String, CondAExpr>) -> CondBExpr {
    match bexpr {
        CondBExpr::True => CondBExpr::True,
        CondBExpr::False => CondBExpr::False,
        CondBExpr::Unop{bexp, op} => CondBExpr::Unop {
            bexp: Box::new(map_bexpr(bexp, mapping)),
            op: op.clone(),
        },
        CondBExpr::BinopA{lhs, rhs, op} => CondBExpr::BinopA {
            lhs: map_aexpr(lhs, mapping),
            rhs: map_aexpr(rhs, mapping),
            op: op.clone(),
        },
        CondBExpr::BinopB{lhs, rhs, op} => CondBExpr::BinopB {
            lhs: Box::new(map_bexpr(lhs, mapping)),
            rhs: Box::new(map_bexpr(rhs, mapping)),
            op: op.clone(),
        },
        CondBExpr::Forall{bindings, condition} => CondBExpr::Forall {
            bindings: bindings.clone(),
            condition: Box::new(map_bexpr(condition, mapping)),
        },
        CondBExpr::Predicate{name, args} => CondBExpr::Predicate {
            name: name.clone(),
            args: args.iter().map(|arg| map_aexpr(arg, mapping)).collect(),
        },
    }
}

fn map_aexpr(aexpr: &CondAExpr, mapping: &HashMap<String, CondAExpr>) -> CondAExpr {
    match aexpr {
        CondAExpr::QualifiedVar{exec, name} => match mapping.get(&qualified_state_var(exec, name)) {
            Some(mapped) => mapped.clone(),
            None => aexpr.clone(),
        },
        CondAExpr::Unop{op: CondAUnop::Address, ..} => aexpr.clone(),
        CondAExpr::Unop{aexp, op} => CondAExpr::Unop {
            aexp: Box::new(map_aexpr(aexp, mapping)),
            op: op.clone(),
        },
        CondAExpr::Cast{ty, aexp} => CondAExpr::Cast {
            ty: ty.clone(),
            aexp: Box::new(map_aexpr(aexp, mapping)),
        },
        CondAExpr::Binop{lhs, rhs, op} => CondAExpr::Binop {
            lhs: Box::new(map_aexpr(lhs, mapping)),
            rhs: Box::new(map_aexpr(rhs, mapping)),
            op: op.clone(),
        },
        CondAExpr::FunCall{name, args} => CondAExpr::FunCall {
            name: name.clone(),
            args: args.iter().map(|arg| map_aexpr(arg, mapping)).collect(),
        },
        CondAExpr::Var(_) | CondAExpr::ReturnValue | CondAExpr::Int(_) | CondAExpr::Float(_) => aexpr.clone(),
    }
}
