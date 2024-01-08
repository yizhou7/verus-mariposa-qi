use builtin_macros::*;
use builtin::*;
mod nl_basics;
use crate::nl_basics::*;
verus! {

pub proof fn auto_0(a0: int, b0: int, c0: int, d0: int,
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
	let temp_0_0 = ((((b0*a0)*(d0*d0))-((b0*d0)*(a0*d0)))*((b0*(b0*c0))*((a0*a0)*(a0+b0))));
	let temp_0_1 = (((b0*(a0*(d0*d0)))-((b0*d0)*(a0*d0)))*((b0*(b0*c0))*((a0*a0)*(a0+b0))));
	assert(temp_0_0 == temp_0_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_1_0 = ((((a1*b1)*(a1-c1))-((b1*c1)*((76 as int)*d1)))*(((b1*b1)*c1)*((b1*a1)+(c1*b1))));
	let temp_1_1 = ((((a1*b1)*(a1-c1))-(((b1*c1)*(76 as int))*d1))*(((b1*b1)*c1)*((b1*a1)+(c1*b1))));
	assert(temp_1_0 == temp_1_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_2_0 = ((((b2*c2)*(d2+b2))*((a2*b2)*(b2*a2)))*(((a2*c2)*(b2*a2))*d2));
	let temp_2_1 = ((((b2*c2)*(d2+b2))*((a2*b2)*(a2*b2)))*(((a2*c2)*(b2*a2))*d2));
	assert(temp_2_0 == temp_2_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_3_0 = ((((a3*c3)-(b3*d3))*((b3-a3)+(c3-b3)))*(((d3*a3)*(c3-d3))*((a3-c3)+(c3*b3))));
	let temp_3_1 = ((((a3*c3)-(b3*d3))*((b3-a3)+(c3-b3)))*((d3*(a3*(c3-d3)))*((a3-c3)+(c3*b3))));
	assert(temp_3_0 == temp_3_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_4_0 = ((((a4*a4)*(d4*a4))*((a4*a4)+(d4*d4)))*(((a4*c4)*(b4*d4))*((b4*b4)*d4)));
	let temp_4_1 = (((((a4*a4)*(d4*a4))*(a4*a4))+(((a4*a4)*(d4*a4))*(d4*d4)))*(((a4*c4)*(b4*d4))*((b4*b4)*d4)));
	assert(temp_4_0 == temp_4_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_5_0 = ((((b5*a5)*(b5*a5))*((d5*c5)*a5))*(((c5-b5)+(d5*b5))-((a5+d5)*(a5*a5))));
	let temp_5_1 = ((((a5*b5)*(b5*a5))*((d5*c5)*a5))*(((c5-b5)+(d5*b5))-((a5+d5)*(a5*a5))));
	assert(temp_5_0 == temp_5_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_6_0 = ((((b6-b6)+(c6*d6))*((c6*b6)*(c6*b6)))*(((a6*d6)-(a6*d6))*((b6*d6)*(c6*d6))));
	let temp_6_1 = ((((b6-b6)+(c6*d6))*((c6*b6)*(b6*c6)))*(((a6*d6)-(a6*d6))*((b6*d6)*(c6*d6))));
	assert(temp_6_0 == temp_6_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_7_0 = ((((b7*d7)-(a7*b7))*((c7*b7)*a7))*(((a7*b7)-(c7+c7))*b7));
	let temp_7_1 = ((((b7*d7)-(a7*b7))*(a7*(c7*b7)))*(((a7*b7)-(c7+c7))*b7));
	assert(temp_7_0 == temp_7_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_8_0 = ((((b8*c8)*(a8*d8))*((c8*c8)+(a8*a8)))*(((a8*d8)*(b8*b8))*((d8*c8)*(b8*b8))));
	let temp_8_1 = ((((b8*c8)*(d8*a8))*((c8*c8)+(a8*a8)))*(((a8*d8)*(b8*b8))*((d8*c8)*(b8*b8))));
	assert(temp_8_0 == temp_8_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_9_0 = (((a9*(c9*a9))*((d9*a9)*(b9*(17 as int))))*(((d9*a9)*(b9*d9))*((b9*b9)*(d9*b9))));
	let temp_9_1 = ((((c9*a9)*a9)*((d9*a9)*(b9*(17 as int))))*(((d9*a9)*(b9*d9))*((b9*b9)*(d9*b9))));
	assert(temp_9_0 == temp_9_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_10_0 = ((((a10*b10)*(b10*c10))*((c10*d10)+(d10*a10)))*(((d10*b10)*(a10+d10))*(d10*(d10*d10))));
	let temp_10_1 = ((((b10*a10)*(b10*c10))*((c10*d10)+(d10*a10)))*(((d10*b10)*(a10+d10))*(d10*(d10*d10))));
	assert(temp_10_0 == temp_10_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_11_0 = ((((d11*a11)*(b11+c11))*((c11*d11)+((81 as int)*c11)))*(((a11*b11)*(d11*c11))*((d11*(18 as int))*(b11*b11))));
	let temp_11_1 = ((((d11*a11)*(b11+c11))*((c11*d11)+((81 as int)*c11)))*(((a11*b11)*(d11*c11))*((d11*(18 as int))*(b11*b11))));
	assert(temp_11_0 == temp_11_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_12_0 = ((b12*((c12*b12)*(b12+d12)))*(((c12-a12)*(b12+d12))*((b12+c12)-(c12*a12))));
	let temp_12_1 = ((((c12*b12)*(b12+d12))*b12)*(((c12-a12)*(b12+d12))*((b12+c12)-(c12*a12))));
	assert(temp_12_0 == temp_12_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_13_0 = ((((c13*c13)*(d13*b13))*((b13*d13)*(d13*a13)))-((((96 as int)*d13)*a13)-((a13*c13)*(b13*c13))));
	let temp_13_1 = (((((c13*c13)*(d13*b13))*(b13*d13))*(d13*a13))-((((96 as int)*d13)*a13)-((a13*c13)*(b13*c13))));
	assert(temp_13_0 == temp_13_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_14_0 = ((((a14*c14)*(d14*c14))*((d14*a14)*(a14*d14)))*(((d14*b14)*(b14*a14))*((c14*b14)-(d14*b14))));
	let temp_14_1 = (((a14*(c14*(d14*c14)))*((d14*a14)*(a14*d14)))*(((d14*b14)*(b14*a14))*((c14*b14)-(d14*b14))));
	assert(temp_14_0 == temp_14_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_15_0 = ((((b15*d15)*(c15*d15))+((a15*c15)*(a15*b15)))+(((b15+d15)*c15)*((a15*b15)*(a15*a15))));
	let temp_15_1 = ((((b15*d15)*(c15*d15))+((c15*a15)*(a15*b15)))+(((b15+d15)*c15)*((a15*b15)*(a15*a15))));
	assert(temp_15_0 == temp_15_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_16_0 = ((((a16*d16)*(a16*b16))-((b16+a16)*(c16+d16)))*((a16*(b16*b16))+((a16*a16)*(d16*c16))));
	let temp_16_1 = ((((a16*d16)*(b16*a16))-((b16+a16)*(c16+d16)))*((a16*(b16*b16))+((a16*a16)*(d16*c16))));
	assert(temp_16_0 == temp_16_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_17_0 = ((((a17*b17)*(b17*a17))*((a17*d17)*(c17-c17)))*(((a17*a17)*(c17*d17))*((c17*(23 as int))*(d17*a17))));
	let temp_17_1 = ((((a17*d17)*(c17-c17))*((a17*b17)*(b17*a17)))*(((a17*a17)*(c17*d17))*((c17*(23 as int))*(d17*a17))));
	assert(temp_17_0 == temp_17_1) by 
			{lemma_mul_properties_auto_1();}// 1

}

} // verus!