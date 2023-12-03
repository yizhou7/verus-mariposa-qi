use builtin_macros::*;
mod nl_basics;
mod calc_auto_only;
mod calc_inst_only;
mod calc_nl_arith_only;
// use builtin::*;
// use vstd::calc_macro::*;

verus! {

// proof fn calc_test(a: int, b: int, c: int)
// {
//     calc! {
//         (==)
//         a;
//         {
//             assume(a == b);
//         }
//         b;
//         {
//             assert(a == b); // ok
//             assume(b == c);
//         }
//         c;
//     }
// }

fn main() {}

} // verus!