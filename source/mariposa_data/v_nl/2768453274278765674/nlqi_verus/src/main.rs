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
	let temp_0_0 = ((b0+((c0-d0)*(d0*d0)))*(b0*((b0*c0)*(b0-b0))));
	let temp_0_1 = ((b0+((d0*d0)*(c0-d0)))*(b0*((b0*c0)*(b0-b0))));
	assert(temp_0_0 == temp_0_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_1_0 = (((((85 as int)-c1)*(b1*c1))-((c1*c1)*(d1*b1)))*((((29 as int)*c1)*(c1*d1))+((c1*c1)*(d1*c1))));
	let temp_1_1 = ((((((85 as int)-c1)*(b1*c1))-((c1*c1)*(d1*b1)))*(((29 as int)*c1)*(c1*d1)))+(((((85 as int)-c1)*(b1*c1))-((c1*c1)*(d1*b1)))*((c1*c1)*(d1*c1))));
	assert(temp_1_0 == temp_1_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_2_0 = ((((b2*c2)+(b2*d2))*((a2+b2)*(c2*c2)))+(((a2*b2)*(b2+c2))*((c2*b2)*(b2*b2))));
	let temp_2_1 = ((((b2*c2)+(b2*d2))*((a2+b2)*(c2*c2)))+(((a2*b2)*(b2+c2))*((b2*b2)*(c2*b2))));
	assert(temp_2_0 == temp_2_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_3_0 = ((((a3+b3)-((85 as int)*a3))*((d3+d3)*(c3*c3)))*(((c3*c3)*(c3*c3))*((d3*c3)*(b3*d3))));
	let temp_3_1 = ((((a3+b3)-((85 as int)*a3))*((c3*c3)*(d3+d3)))*(((c3*c3)*(c3*c3))*((d3*c3)*(b3*d3))));
	assert(temp_3_0 == temp_3_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_4_0 = ((((a4*b4)*b4)*((d4-d4)*(c4-c4)))*(((a4*b4)*(c4-c4))+((b4*b4)*(d4+a4))));
	let temp_4_1 = ((((a4*b4)*b4)*((d4-d4)*(c4-c4)))*(((b4*a4)*(c4-c4))+((b4*b4)*(d4+a4))));
	assert(temp_4_0 == temp_4_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_5_0 = ((((b5*a5)*(c5*a5))-(((98 as int)+c5)*(d5*b5)))-(((c5*a5)*(a5*c5))*((d5*b5)*(c5*(54 as int)))));
	let temp_5_1 = ((((b5*a5)*(a5*c5))-(((98 as int)+c5)*(d5*b5)))-(((c5*a5)*(a5*c5))*((d5*b5)*(c5*(54 as int)))));
	assert(temp_5_0 == temp_5_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_6_0 = ((d6*c6)*(((c6*c6)*c6)*c6));
	let temp_6_1 = ((d6*c6)*(c6*((c6*c6)*c6)));
	assert(temp_6_0 == temp_6_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_7_0 = (a7*(((c7*b7)*(a7*c7))*((b7*c7)*(b7+a7))));
	let temp_7_1 = (a7*(((a7*c7)*(c7*b7))*((b7*c7)*(b7+a7))));
	assert(temp_7_0 == temp_7_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_8_0 = ((((b8-c8)*(a8*b8))*((c8+d8)*a8))*(((a8*b8)+(c8*b8))*((d8+a8)*(a8*d8))));
	let temp_8_1 = (((b8-c8)*((a8*b8)*((c8+d8)*a8)))*(((a8*b8)+(c8*b8))*((d8+a8)*(a8*d8))));
	assert(temp_8_0 == temp_8_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_9_0 = ((((d9*a9)*((52 as int)*d9))*((c9*c9)*(d9*b9)))*(((a9*a9)-(c9*c9))*((d9*a9)*((20 as int)*a9))));
	let temp_9_1 = (((((52 as int)*d9)*(d9*a9))*((c9*c9)*(d9*b9)))*(((a9*a9)-(c9*c9))*((d9*a9)*((20 as int)*a9))));
	assert(temp_9_0 == temp_9_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_10_0 = (((a10*(b10+b10))*((b10-b10)*(a10*c10)))*(((c10-d10)*(a10*c10))-((c10+a10)*(b10*d10))));
	let temp_10_1 = (((a10*(b10+b10))*((b10-b10)*(a10*c10)))*(((c10-d10)*(a10*c10))-((c10+a10)*(d10*b10))));
	assert(temp_10_0 == temp_10_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_11_0 = ((((d11*a11)*(b11*c11))*((a11*a11)*(b11-b11)))*d11);
	let temp_11_1 = ((((d11*a11)*(b11*c11))*(a11*(a11*(b11-b11))))*d11);
	assert(temp_11_0 == temp_11_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_12_0 = ((((b12*c12)+(d12*a12))*(((15 as int)*c12)-(d12*c12)))*(((b12*a12)*(b12+b12))*((b12*a12)*(a12*b12))));
	let temp_12_1 = ((((b12*c12)+(d12*a12))*(((15 as int)*c12)-(d12*c12)))*(((b12*a12)*(b12+b12))*((a12*b12)*(b12*a12))));
	assert(temp_12_0 == temp_12_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_13_0 = ((((a13*a13)*(b13*c13))*((d13*d13)*(c13*d13)))-((b13*(a13*b13))*((b13*a13)*(d13*c13))));
	let temp_13_1 = (((((a13*a13)*b13)*c13)*((d13*d13)*(c13*d13)))-((b13*(a13*b13))*((b13*a13)*(d13*c13))));
	assert(temp_13_0 == temp_13_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_14_0 = ((((d14*c14)*c14)-((c14*c14)+(c14+c14)))*(((b14*d14)*(a14*c14))*((c14*d14)*(b14*c14))));
	let temp_14_1 = ((((d14*c14)*c14)-((c14*c14)+(c14+c14)))*(((b14*d14)*(a14*c14))*(((c14*d14)*b14)*c14)));
	assert(temp_14_0 == temp_14_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_15_0 = ((((b15*b15)*(d15*b15))*((a15+c15)*(b15*a15)))-(((c15*d15)*(d15*a15))*((a15*c15)-(c15*c15))));
	let temp_15_1 = ((((b15*b15)*(d15*b15))*((a15+c15)*(b15*a15)))-((((c15*d15)*d15)*a15)*((a15*c15)-(c15*c15))));
	assert(temp_15_0 == temp_15_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_16_0 = ((((a16*b16)*(c16*b16))*(((0 as int)*d16)-(b16*a16)))*(((c16*a16)*(a16+a16))*(c16*(a16*d16))));
	let temp_16_1 = ((((a16*b16)*(c16*b16))*(((0 as int)*d16)-(b16*a16)))*((c16*(a16*d16))*((c16*a16)*(a16+a16))));
	assert(temp_16_0 == temp_16_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_17_0 = (((((46 as int)*b17)*(d17*c17))+(b17*(d17+a17)))*(((d17-b17)*(d17*d17))*(((67 as int)*a17)*(b17*d17))));
	let temp_17_1 = ((((d17-b17)*(d17*d17))*(((67 as int)*a17)*(b17*d17)))*((((46 as int)*b17)*(d17*c17))+(b17*(d17+a17))));
	assert(temp_17_0 == temp_17_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_18_0 = ((((d18+c18)+(d18-d18))*((b18*b18)-(c18*b18)))-c18);
	let temp_18_1 = ((((b18*b18)-(c18*b18))*((d18+c18)+(d18-d18)))-c18);
	assert(temp_18_0 == temp_18_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_19_0 = ((((d19*(48 as int))+(d19+d19))*((b19*c19)-(b19-d19)))*(d19*(((50 as int)*c19)*(b19+a19))));
	let temp_19_1 = ((((b19*c19)-(b19-d19))*((d19*(48 as int))+(d19+d19)))*(d19*(((50 as int)*c19)*(b19+a19))));
	assert(temp_19_0 == temp_19_1) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_20_0 = ((((c20*d20)*(b20*d20))*((a20-c20)*(d20*c20)))*(((b20*c20)*(b20*c20))-(((22 as int)*a20)*(b20*b20))));
	let temp_20_1 = ((((c20*d20)*(b20*d20))*((a20-c20)*(d20*c20)))*(((b20*c20)*(c20*b20))-(((22 as int)*a20)*(b20*b20))));
	assert(temp_20_0 == temp_20_1) by 
			{lemma_mul_properties_auto_1();}// 1

}

} // verus!