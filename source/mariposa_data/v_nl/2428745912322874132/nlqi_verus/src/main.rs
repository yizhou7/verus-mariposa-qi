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
	let temp_0_0 = ((((d0*d0)-(b0+c0))*((d0*d0)*(b0-d0)))*(((b0*b0)*(a0*d0))*((a0*b0)*(c0*a0))));
	let temp_0_1 = ((((d0*d0)-(b0+c0))*((d0*d0)*(b0-d0)))*(((b0*b0)*(a0*d0))*(a0*(b0*(c0*a0)))));
	assert(temp_0_0 == temp_0_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_1_0 = ((((a1*(23 as int))*(c1*d1))*((a1-c1)*(b1*c1)))+(((a1*b1)*(c1*a1))*((a1+b1)*(d1*a1))));
	let temp_1_1 = (((((23 as int)*a1)*(c1*d1))*((a1-c1)*(b1*c1)))+(((a1*b1)*(c1*a1))*((a1+b1)*(d1*a1))));
	assert(temp_1_0 == temp_1_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_2_0 = ((((d2-d2)*(c2-d2))*((b2+a2)*(c2*d2)))+(((d2*c2)*c2)*d2));
	let temp_2_1 = ((((d2-d2)*(c2-d2))*((b2+a2)*(c2*d2)))+((c2*(d2*c2))*d2));
	assert(temp_2_0 == temp_2_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_3_0 = ((((b3*d3)*(b3*a3))*((d3*b3)*(b3*a3)))+(((a3+c3)*(d3*a3))*((c3*d3)*(b3*d3))));
	let temp_3_1 = ((((b3*a3)*(b3*d3))*((d3*b3)*(b3*a3)))+(((a3+c3)*(d3*a3))*((c3*d3)*(b3*d3))));
	assert(temp_3_0 == temp_3_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_4_0 = (((a4-(b4*b4))*c4)+(((b4*c4)-(a4*d4))*((d4*a4)*(d4*(45 as int)))));
	let temp_4_1 = (((a4-(b4*b4))*c4)+(((b4*c4)-(d4*a4))*((d4*a4)*(d4*(45 as int)))));
	assert(temp_4_0 == temp_4_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_5_0 = ((((b5+d5)*(c5+b5))*((a5*a5)*(c5*d5)))*(((c5*c5)*(c5*b5))*(((56 as int)*a5)-(a5*d5))));
	let temp_5_1 = ((((b5+d5)*(c5+b5))*((a5*a5)*(c5*d5)))*((c5*(c5*(c5*b5)))*(((56 as int)*a5)-(a5*d5))));
	assert(temp_5_0 == temp_5_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_6_0 = ((((d6*d6)*(a6*c6))*((a6-a6)+(c6*c6)))*(((a6+d6)*(d6*b6))-((a6*c6)*(a6*a6))));
	let temp_6_1 = (((((d6*d6)*(a6*c6))*((a6-a6)+(c6*c6)))*((a6+d6)*(d6*b6)))-((((d6*d6)*(a6*c6))*((a6-a6)+(c6*c6)))*((a6*c6)*(a6*a6))));
	assert(temp_6_0 == temp_6_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_7_0 = ((((b7+b7)-(a7-b7))*((d7*b7)*(a7*b7)))*(((b7*c7)*(a7*b7))*((c7*d7)+a7)));
	let temp_7_1 = ((((b7+b7)*((d7*b7)*(a7*b7)))-((a7-b7)*((d7*b7)*(a7*b7))))*(((b7*c7)*(a7*b7))*((c7*d7)+a7)));
	assert(temp_7_0 == temp_7_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_8_0 = ((((b8*a8)*(c8*b8))*((d8-b8)-(d8*c8)))+((((12 as int)*a8)*(d8*b8))*a8));
	let temp_8_1 = ((((b8*a8)*(b8*c8))*((d8-b8)-(d8*c8)))+((((12 as int)*a8)*(d8*b8))*a8));
	assert(temp_8_0 == temp_8_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_9_0 = ((((b9*a9)*(d9*c9))*(a9*(a9*b9)))*(((c9*c9)*(b9+a9))*((b9*b9)*(a9*a9))));
	let temp_9_1 = (((b9*a9)*((d9*c9)*(a9*(a9*b9))))*(((c9*c9)*(b9+a9))*((b9*b9)*(a9*a9))));
	assert(temp_9_0 == temp_9_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_10_0 = ((((d10+c10)*(a10*a10))*((d10*d10)*(d10+d10)))*(((a10*b10)-(a10+b10))*((d10*c10)*(c10*d10))));
	let temp_10_1 = ((((a10*b10)-(a10+b10))*((d10*c10)*(c10*d10)))*(((d10+c10)*(a10*a10))*((d10*d10)*(d10+d10))));
	assert(temp_10_0 == temp_10_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_11_0 = ((((c11*a11)*(a11*b11))*((d11*c11)+(a11*d11)))*(((a11*b11)*(b11-d11))*((b11*d11)*(c11-c11))));
	let temp_11_1 = ((((a11*b11)*(c11*a11))*((d11*c11)+(a11*d11)))*(((a11*b11)*(b11-d11))*((b11*d11)*(c11-c11))));
	assert(temp_11_0 == temp_11_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_12_0 = ((((d12*a12)*(a12*a12))*((d12+d12)*(b12*b12)))*(((b12*d12)*(b12*b12))*((b12*(66 as int))*(d12*c12))));
	let temp_12_1 = ((((d12*a12)*(a12*a12))*((d12+d12)*(b12*b12)))*((((b12*d12)*b12)*b12)*((b12*(66 as int))*(d12*c12))));
	assert(temp_12_0 == temp_12_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_13_0 = ((((a13*(39 as int))+(b13*a13))*((a13*d13)+(a13*a13)))*((a13*(a13*d13))*((c13-b13)*(d13*d13))));
	let temp_13_1 = ((((a13*(39 as int))+(b13*a13))*((a13*d13)+(a13*a13)))*((a13*(a13*d13))*((d13*d13)*(c13-b13))));
	assert(temp_13_0 == temp_13_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_14_0 = ((((d14+c14)*(a14*d14))*((b14*b14)*(d14*c14)))-(((b14*b14)*(c14*d14))-((c14*a14)*b14)));
	let temp_14_1 = ((((d14+c14)*(a14*d14))*((b14*b14)*(d14*c14)))-(((c14*d14)*(b14*b14))-((c14*a14)*b14)));
	assert(temp_14_0 == temp_14_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_15_0 = ((((a15*a15)*(d15*b15))*((c15*b15)*(b15+(72 as int))))*(a15+(((91 as int)*a15)*(a15*d15))));
	let temp_15_1 = ((a15+(((91 as int)*a15)*(a15*d15)))*(((a15*a15)*(d15*b15))*((c15*b15)*(b15+(72 as int)))));
	assert(temp_15_0 == temp_15_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_16_0 = ((((d16*b16)*(a16+d16))*((d16*d16)*(b16-a16)))*(((c16*d16)*(b16*a16))*((d16*a16)*(b16*a16))));
	let temp_16_1 = (((d16*(b16*(a16+d16)))*((d16*d16)*(b16-a16)))*(((c16*d16)*(b16*a16))*((d16*a16)*(b16*a16))));
	assert(temp_16_0 == temp_16_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_17_0 = ((((d17*b17)*(a17*b17))*((56 as int)*(a17*d17)))*(((d17*d17)*(b17+d17))*((c17*a17)*(a17*b17))));
	let temp_17_1 = ((((d17*b17)*(a17*b17))*((56 as int)*(a17*d17)))*(((d17*d17)*(b17+d17))*((c17*a17)*(a17*b17))));
	assert(temp_17_0 == temp_17_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_18_0 = ((((b18*a18)*(c18*c18))*((c18-d18)*d18))*(((a18*c18)-(b18*a18))*((b18-a18)*(b18-c18))));
	let temp_18_1 = ((((b18*a18)*(c18*c18))*((c18-d18)*d18))*(((a18*c18)-(b18*a18))*((b18-c18)*(b18-a18))));
	assert(temp_18_0 == temp_18_1) by 
			{lemma_mul_properties_auto_1();}// 1

}

} // verus!