use builtin_macros::*;
use builtin::*;
use crate::nl_basics::*;
verus! {

pub proof fn inst_only_0(a: int, b: int, c: int, d: int)
{
	let temp_0_0 = ((d*d)*(c*d));
	let temp_0_1 = (((d*d)*c)*d);
	assert(temp_0_0 == temp_0_1) by 
			{lemma_mul_is_associative((d*d), c, d);}// 1
	let temp_1_0 = ((c*c)*(c*d));
	let temp_1_1 = (c*(c*(c*d)));
	assert(temp_1_0 == temp_1_1) by 
			{lemma_mul_is_associative(c, c, (c*d));}// 1
	let temp_2_0 = ((c*d)*(b*a));
	let temp_2_1 = ((b*a)*(c*d));
	assert(temp_2_0 == temp_2_1) by 
			{lemma_mul_is_commutative((c*d), (b*a));}// 1

}
} // verus!