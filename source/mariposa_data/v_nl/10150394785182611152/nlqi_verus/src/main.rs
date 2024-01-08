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
	let temp_0_0 = ((((b0+a0)*(b0*d0))*(((45 as int)*a0)*(a0*c0)))*(((d0*c0)*(b0*(68 as int)))-((c0*c0)*(b0*d0))));
	let temp_0_1 = ((((b0*(b0*d0))+(a0*(b0*d0)))*(((45 as int)*a0)*(a0*c0)))*(((d0*c0)*(b0*(68 as int)))-((c0*c0)*(b0*d0))));
	assert(temp_0_0 == temp_0_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_1_0 = ((((a1*b1)-c1)+((d1+a1)-(c1+(64 as int))))*(((b1+a1)*(d1*c1))*((a1*d1)-(c1*a1))));
	let temp_1_1 = ((((b1*a1)-c1)+((d1+a1)-(c1+(64 as int))))*(((b1+a1)*(d1*c1))*((a1*d1)-(c1*a1))));
	assert(temp_1_0 == temp_1_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_2_0 = ((((a2+b2)*(b2*c2))*((c2*d2)-(a2*d2)))*(((b2*c2)*(c2*b2))*(d2*(c2*b2))));
	let temp_2_1 = ((((a2+b2)*(b2*c2))*((c2*d2)-(a2*d2)))*(((b2*c2)*(c2*b2))*(d2*(b2*c2))));
	assert(temp_2_0 == temp_2_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_3_0 = ((((c3*b3)*(c3+d3))*((d3*c3)*(c3*c3)))*(((a3*b3)*(d3+c3))*((b3-c3)*(a3*c3))));
	let temp_3_1 = ((((c3*b3)*(c3+d3))*((d3*c3)*(c3*c3)))*((((a3*b3)*d3)+((a3*b3)*c3))*((b3-c3)*(a3*c3))));
	assert(temp_3_0 == temp_3_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_4_0 = ((((b4-c4)*(a4*a4))*((a4*b4)*(d4*a4)))-(((b4+d4)*(d4*d4))*((a4*b4)*(d4*d4))));
	let temp_4_1 = ((((a4*a4)*(b4-c4))*((a4*b4)*(d4*a4)))-(((b4+d4)*(d4*d4))*((a4*b4)*(d4*d4))));
	assert(temp_4_0 == temp_4_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_5_0 = ((((c5*b5)*(a5*c5))*((c5*c5)*(d5*c5)))*(b5+((d5*b5)+(a5*b5))));
	let temp_5_1 = (((((c5*b5)*(a5*c5))*(c5*c5))*(d5*c5))*(b5+((d5*b5)+(a5*b5))));
	assert(temp_5_0 == temp_5_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_6_0 = ((b6*(35 as int))+(((d6*b6)*(a6*c6))*((d6*(35 as int))*(d6-a6))));
	let temp_6_1 = ((b6*(35 as int))+(((d6*b6)*(a6*c6))*(((35 as int)*d6)*(d6-a6))));
	assert(temp_6_0 == temp_6_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_7_0 = ((((b7*c7)*(d7*c7))*((d7-c7)*a7))*(((c7*(95 as int))*(c7*a7))*((b7*d7)-(a7*c7))));
	let temp_7_1 = ((((b7*c7)*(d7*c7))*((d7-c7)*a7))*(((c7*(95 as int))*(c7*a7))*((d7*b7)-(a7*c7))));
	assert(temp_7_0 == temp_7_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_8_0 = ((((b8*d8)*((19 as int)*b8))*((c8-a8)*(b8-b8)))*(((c8*a8)-(b8*b8))*((b8*a8)*(a8*a8))));
	let temp_8_1 = (((((b8*d8)*((19 as int)*b8))*(c8-a8))*(b8-b8))*(((c8*a8)-(b8*b8))*((b8*a8)*(a8*a8))));
	assert(temp_8_0 == temp_8_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_9_0 = ((((b9*d9)*(b9+a9))*((a9*a9)*(c9*d9)))*(((b9+c9)*(c9*a9))*((d9*c9)*(c9-c9))));
	let temp_9_1 = ((((b9*d9)*(b9+a9))*((a9*a9)*(c9*d9)))*((b9+c9)*((c9*a9)*((d9*c9)*(c9-c9)))));
	assert(temp_9_0 == temp_9_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_10_0 = ((((a10*c10)*(d10*d10))*((c10*c10)*(c10*c10)))*(((d10*a10)*c10)*((d10*c10)*a10)));
	let temp_10_1 = ((((a10*c10)*(d10*d10))*((c10*c10)*(c10*c10)))*(((d10*a10)*c10)*(a10*(d10*c10))));
	assert(temp_10_0 == temp_10_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_11_0 = ((((a11*d11)*(a11*b11))*((d11*d11)*(d11*c11)))*(((a11*a11)*(c11+d11))*((a11*b11)+(c11-b11))));
	let temp_11_1 = ((((a11*d11)*(a11*b11))*((d11*d11)*(d11*c11)))*(((a11*b11)+(c11-b11))*((a11*a11)*(c11+d11))));
	assert(temp_11_0 == temp_11_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_12_0 = ((((a12-a12)*(a12*c12))-((b12*a12)*(d12*d12)))*(((c12*a12)+(c12*c12))*((d12+d12)-(c12*a12))));
	let temp_12_1 = ((((a12-a12)*(a12*c12))-((b12*a12)*(d12*d12)))*(((c12*a12)+(c12*c12))*((d12+d12)-(c12*a12))));
	assert(temp_12_0 == temp_12_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_13_0 = (c13+(((d13*a13)-(d13*a13))*((b13*a13)*(b13*b13))));
	let temp_13_1 = (c13+(((d13*a13)-(a13*d13))*((b13*a13)*(b13*b13))));
	assert(temp_13_0 == temp_13_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_14_0 = ((((b14-c14)+(a14*c14))*((d14*d14)*(b14-b14)))+(((a14*b14)+(b14-c14))*((a14+b14)*(c14*c14))));
	let temp_14_1 = ((((b14-c14)+(a14*c14))*((d14*d14)*(b14-b14)))+(((a14+b14)*(c14*c14))*((a14*b14)+(b14-c14))));
	assert(temp_14_0 == temp_14_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_15_0 = ((((b15*c15)*(d15*c15))*((b15*c15)*(c15*b15)))*(((a15*c15)*(b15*c15))*((c15*a15)*(b15*(27 as int)))));
	let temp_15_1 = (((b15*(c15*(d15*c15)))*((b15*c15)*(c15*b15)))*(((a15*c15)*(b15*c15))*((c15*a15)*(b15*(27 as int)))));
	assert(temp_15_0 == temp_15_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_16_0 = (((((79 as int)*a16)*(a16*d16))*((d16*c16)*(b16*c16)))*(((d16*d16)+(a16*a16))+((a16-c16)*(b16*d16))));
	let temp_16_1 = ((((((79 as int)*a16)*(a16*d16))*((d16*c16)*(b16*c16)))*((d16*d16)+(a16*a16)))+(((((79 as int)*a16)*(a16*d16))*((d16*c16)*(b16*c16)))*((a16-c16)*(b16*d16))));
	assert(temp_16_0 == temp_16_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_17_0 = ((b17-((c17*c17)*(b17+d17)))*(((d17*c17)*(b17*b17))*((c17*d17)*(b17*c17))));
	let temp_17_1 = ((b17-((c17*c17)*(b17+d17)))*(((c17*d17)*(b17*b17))*((c17*d17)*(b17*c17))));
	assert(temp_17_0 == temp_17_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_18_0 = (((c18*c18)*((d18*b18)*(d18*d18)))*(((b18*c18)*(c18*c18))*(a18*(c18*c18))));
	let temp_18_1 = (((c18*c18)*((d18*b18)*(d18*d18)))*(((b18*c18)*(c18*c18))*(a18*(c18*c18))));
	assert(temp_18_0 == temp_18_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_19_0 = ((((b19*b19)*(a19-b19))*((b19*b19)*(c19+a19)))*(((c19*b19)*(b19+a19))*((b19*a19)*(c19*a19))));
	let temp_19_1 = ((((b19*b19)*(a19-b19))*((c19+a19)*(b19*b19)))*(((c19*b19)*(b19+a19))*((b19*a19)*(c19*a19))));
	assert(temp_19_0 == temp_19_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_20_0 = ((((a20*b20)*(b20*c20))*((b20*a20)*(d20*d20)))-(((d20*d20)-b20)*((d20*a20)*(c20*c20))));
	let temp_20_1 = ((((a20*b20)*(b20*c20))*((b20*a20)*(d20*d20)))-(((d20*d20)-b20)*(((d20*a20)*c20)*c20)));
	assert(temp_20_0 == temp_20_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_21_0 = ((((a21-d21)*(d21+a21))*((b21*a21)*(c21*a21)))*(((a21*d21)*(d21*a21))*(d21*(c21*d21))));
	let temp_21_1 = ((((a21*(d21+a21))-(d21*(d21+a21)))*((b21*a21)*(c21*a21)))*(((a21*d21)*(d21*a21))*(d21*(c21*d21))));
	assert(temp_21_0 == temp_21_1) by 
			{lemma_mul_properties_auto_1();}// 1

}

} // verus!