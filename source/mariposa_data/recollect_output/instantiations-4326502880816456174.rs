use builtin_macros::*;
use builtin::*;
mod nl_basics;
use crate::nl_basics::*;
verus! {

pub proof fn free_0(a0: int, b0: int, c0: int, d0: int,
a1: int, b1: int, c1: int, d1: int,
a2: int, b2: int, c2: int, d2: int,
a3: int, b3: int, c3: int, d3: int,
a4: int, b4: int, c4: int, d4: int,
a5: int, b5: int, c5: int, d5: int,
a6: int, b6: int, c6: int, d6: int,
a7: int, b7: int, c7: int, d7: int,
a8: int, b8: int, c8: int, d8: int,
a9: int, b9: int, c9: int, d9: int,
a10: int, b10: int, c10: int, d10: int,
a11: int, b11: int, c11: int, d11: int,
a12: int, b12: int, c12: int, d12: int,
a13: int, b13: int, c13: int, d13: int,
a14: int, b14: int, c14: int, d14: int,
a15: int, b15: int, c15: int, d15: int,
a16: int, b16: int, c16: int, d16: int,
a17: int, b17: int, c17: int, d17: int,
a18: int, b18: int, c18: int, d18: int,
a19: int, b19: int, c19: int, d19: int,
a20: int, b20: int, c20: int, d20: int,
a21: int, b21: int, c21: int, d21: int,
a22: int, b22: int, c22: int, d22: int,
a23: int, b23: int, c23: int, d23: int,
a24: int, b24: int, c24: int, d24: int,
a25: int, b25: int, c25: int, d25: int,
a26: int, b26: int, c26: int, d26: int,
a27: int, b27: int, c27: int, d27: int,
a28: int, b28: int, c28: int, d28: int,
a29: int, b29: int, c29: int, d29: int)
{
	let temp_0_0 = ((((b0-d0)-(c0*a0))-((c0*b0)*(c0+b0)))-(((a0-d0)*(c0*c0))*((b0*b0)*(d0+c0))));
	let temp_0_1 = ((((b0-d0)-(c0*a0))-((c0*b0)*(c0+b0)))-(((a0-d0)*(c0*c0))*(b0*(b0*(d0+c0)))));
	assert(temp_0_0 == temp_0_1) by {
		lemma_mul_is_associative(b0, b0, d0 + c0);
	}
	let temp_1_0 = ((((a1*d1)*(b1*d1))*((a1*d1)*(a1*(23 as int))))*(6 as int));
	let temp_1_1 = ((((a1*d1)*(b1*d1))*((a1*(23 as int))*(a1*d1)))*(6 as int));
	assert(temp_1_0 == temp_1_1) by {
		lemma_mul_is_commutative(a1 * 23, a1 * d1);
	}
	let temp_2_0 = ((((a2*(99 as int))*(c2*d2))-((a2*c2)*(b2*a2)))*(((b2*d2)*(d2*c2))*(((23 as int)*a2)*(b2*c2))));
	let temp_2_1 = (((a2*((99 as int)*(c2*d2)))-((a2*c2)*(b2*a2)))*(((b2*d2)*(d2*c2))*(((23 as int)*a2)*(b2*c2))));
	assert(temp_2_0 == temp_2_1) by {
		lemma_mul_is_associative(a2, 99, c2 * d2);
	}
	let temp_3_0 = (b3-((((40 as int)*b3)*(d3*d3))*((b3*b3)*(b3*d3))));
	let temp_3_1 = (b3-((((40 as int)*b3)*(d3*d3))*((b3*b3)*(b3*d3))));
	assert(temp_3_0 == temp_3_1);
	let temp_4_0 = ((((c4-(94 as int))*(c4*d4))*((d4+a4)*(a4+d4)))+(((c4*a4)+(b4*a4))*((b4*d4)*(c4*a4))));
	let temp_4_1 = (((((c4-(94 as int))*c4)*d4)*((d4+a4)*(a4+d4)))+(((c4*a4)+(b4*a4))*((b4*d4)*(c4*a4))));
	assert(temp_4_0 == temp_4_1) by {
		lemma_mul_is_associative(c4 - 94, c4, d4);
	}

}

} // verus!