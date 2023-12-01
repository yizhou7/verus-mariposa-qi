use builtin_macros::*;
use builtin::*;
verus! {
pub proof fn lemma_test(a: int, b: int, c: int) by (nonlinear_arith) {}
} // verus!