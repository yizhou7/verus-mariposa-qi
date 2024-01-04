use builtin_macros::*;
use builtin::*;
mod nl_basics;
use crate::nl_basics::*;
verus! {

pub proof fn nlarith_0(a0: int, b0: int, c0: int, d0: int,
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
a19: int, b19: int, c19: int, d19: int)
{
	let temp_0_0 = (((a0*((c0*a0)*(c0*b0)))*(d0*((a0*d0)*(d0*d0))))+((c0*((a0*c0)+(c0*d0)))*((a0*(c0*c0))*((d0-d0)*(a0*a0)))));
	let temp_0_1 = (((d0*((a0*d0)*(d0*d0)))*(a0*((c0*a0)*(c0*b0))))+((c0*((a0*c0)+(c0*d0)))*((a0*(c0*c0))*((d0-d0)*(a0*a0)))));
	assert(temp_0_0 == temp_0_1);
	let temp_1_0 = (((((a1*d1)-(d1+a1))*((a1+b1)*(c1*c1)))*(((b1*a1)-(b1*c1))*((d1*a1)-(d1+b1))))+((((b1-a1)*(b1*b1))*((d1-b1)-(b1*b1)))-(((a1*b1)*(b1*a1))*((a1*a1)*(d1*a1)))));
	let temp_1_1 = (((((a1*d1)-(d1+a1))*((c1*c1)*(a1+b1)))*(((b1*a1)-(b1*c1))*((d1*a1)-(d1+b1))))+((((b1-a1)*(b1*b1))*((d1-b1)-(b1*b1)))-(((a1*b1)*(b1*a1))*((a1*a1)*(d1*a1)))));
	assert(temp_1_0 == temp_1_1);
	let temp_2_0 = ((((c2-(a2*d2))*((a2*b2)-(a2*d2)))*(((d2*c2)*(c2*c2))*((a2-a2)*(b2*b2))))*((((b2+a2)*(b2*a2))*(b2+(d2*b2)))*(((c2*c2)+(a2*a2))*((a2*a2)*(b2*b2)))));
	let temp_2_1 = ((((c2-(a2*d2))*((a2*b2)-(a2*d2)))*((((d2*c2)*(c2*c2))*(a2-a2))*(b2*b2)))*((((b2+a2)*(b2*a2))*(b2+(d2*b2)))*(((c2*c2)+(a2*a2))*((a2*a2)*(b2*b2)))));
	assert(temp_2_0 == temp_2_1);
	let temp_3_0 = (b3*(d3*((d3+(a3*a3))*((d3*c3)-(c3*a3)))));
	let temp_3_1 = (b3*(d3*((d3*((d3*c3)-(c3*a3)))+((a3*a3)*((d3*c3)-(c3*a3))))));
	assert(temp_3_0 == temp_3_1);
	let temp_4_0 = ((((a4*(b4*b4))*(b4-(a4*b4)))*(((23 as int)*(d4*d4))-((b4*d4)*((32 as int)*a4))))*((((c4-b4)*(a4*a4))*((c4*c4)*(a4*c4)))*((c4-(b4+(8 as int)))*(c4*(c4*a4)))));
	let temp_4_1 = (((((a4*(b4*b4))*(b4-(a4*b4)))*((23 as int)*(d4*d4)))-(((a4*(b4*b4))*(b4-(a4*b4)))*((b4*d4)*((32 as int)*a4))))*((((c4-b4)*(a4*a4))*((c4*c4)*(a4*c4)))*((c4-(b4+(8 as int)))*(c4*(c4*a4)))));
	assert(temp_4_0 == temp_4_1);
	let temp_5_0 = (((((d5*b5)*(d5*c5))*((d5*c5)*(c5*c5)))*(((c5*b5)*c5)*((b5*c5)*(b5*d5))))*((((d5*a5)*(d5*a5))*d5)*(((c5*b5)*(a5*a5))*((b5*c5)*(a5-d5)))));
	let temp_5_1 = (((((c5*b5)*c5)*((b5*c5)*(b5*d5)))*(((d5*b5)*(d5*c5))*((d5*c5)*(c5*c5))))*((((d5*a5)*(d5*a5))*d5)*(((c5*b5)*(a5*a5))*((b5*c5)*(a5-d5)))));
	assert(temp_5_0 == temp_5_1);
	let temp_6_0 = (((((a6*d6)*(c6*b6))-(b6+(a6*c6)))*(((a6*d6)*(a6*c6))*((a6*c6)*(a6+a6))))*(((a6*(c6*d6))*((b6*a6)*(c6*d6)))*(((d6*d6)*(d6-d6))*((d6*c6)*(a6*d6)))));
	let temp_6_1 = (((((a6*d6)*(a6*c6))*((a6*c6)*(a6+a6)))*(((a6*d6)*(c6*b6))-(b6+(a6*c6))))*(((a6*(c6*d6))*((b6*a6)*(c6*d6)))*(((d6*d6)*(d6-d6))*((d6*c6)*(a6*d6)))));
	assert(temp_6_0 == temp_6_1);
	let temp_7_0 = (((((b7*c7)*(b7*c7))*((a7*a7)*((16 as int)+a7)))*((c7*(d7+c7))*((b7*d7)*(a7*a7))))*((d7*((b7*(66 as int))*(b7-b7)))*(((a7*d7)-(a7*b7))*((b7*b7)*(b7*a7)))));
	let temp_7_1 = (((((b7*c7)*(b7*c7))*((a7*a7)*((16 as int)+a7)))*((c7*(d7+c7))*((b7*d7)*(a7*a7))))*((d7*((b7*(66 as int))*(b7-b7)))*(((d7*a7)-(a7*b7))*((b7*b7)*(b7*a7)))));
	assert(temp_7_0 == temp_7_1);
	let temp_8_0 = ((a8-(((b8*d8)*(c8*c8))*((b8*b8)*(d8*b8))))*((((d8*b8)*(b8*d8))+((b8*a8)*(b8*a8)))*(((c8*b8)*(a8*d8))*((b8+b8)*(a8*c8)))));
	let temp_8_1 = ((a8-(((b8*d8)*(c8*c8))*((b8*b8)*(d8*b8))))*((((d8*b8)*(b8*d8))*(((c8*b8)*(a8*d8))*((b8+b8)*(a8*c8))))+(((b8*a8)*(b8*a8))*(((c8*b8)*(a8*d8))*((b8+b8)*(a8*c8))))));
	assert(temp_8_0 == temp_8_1);
	let temp_9_0 = (((((d9*a9)*(c9*d9))*((c9*d9)*(a9*d9)))*(((d9-b9)*b9)*((c9*d9)*(b9*a9))))-((((a9-c9)*(a9*b9))+((a9*d9)*(a9*d9)))*(((b9*b9)*(b9*c9))*((b9*b9)*(b9*c9)))));
	let temp_9_1 = (((((d9*a9)*(c9*d9))*((c9*d9)*(a9*d9)))*(((d9-b9)*b9)*((c9*d9)*(b9*a9))))-((((a9-c9)*(a9*b9))+((a9*d9)*(a9*d9)))*(((b9*b9)*(b9*c9))*((b9*b9)*(b9*c9)))));
	assert(temp_9_0 == temp_9_1);
	let temp_10_0 = (((((d10*c10)*(d10-c10))+((d10+b10)+(c10*a10)))*(((c10*a10)*(b10-d10))*((c10*c10)*(c10*d10))))-(((a10-(b10*c10))-((c10*b10)*(a10*c10)))*(((d10*a10)*((36 as int)*d10))*((a10*b10)*(a10*d10)))));
	let temp_10_1 = (((((d10*c10)*(d10-c10))+((d10+b10)+(c10*a10)))*(((c10*a10)*(b10-d10))*((c10*c10)*(c10*d10))))-(((a10-(b10*c10))-((a10*c10)*(c10*b10)))*(((d10*a10)*((36 as int)*d10))*((a10*b10)*(a10*d10)))));
	assert(temp_10_0 == temp_10_1);
	let temp_11_0 = ((((b11*(a11*a11))*((c11-c11)*a11))*(((a11+b11)*a11)+(a11-(d11*b11))))-((((b11*b11)+(c11+d11))*((d11*c11)-(a11-b11)))*((b11-(a11*a11))-c11)));
	let temp_11_1 = (((b11*(a11*a11))*(((c11-c11)*a11)*(((a11+b11)*a11)+(a11-(d11*b11)))))-((((b11*b11)+(c11+d11))*((d11*c11)-(a11-b11)))*((b11-(a11*a11))-c11)));
	assert(temp_11_0 == temp_11_1);
	let temp_12_0 = ((b12*(((c12*b12)*(a12*d12))*(c12*(b12*a12))))*((((d12*b12)-(b12-a12))*((c12*c12)*(a12*(12 as int))))*(((c12-(92 as int))*(b12*b12))+((a12*a12)*(c12*(78 as int))))));
	let temp_12_1 = (((b12*((c12*b12)*(a12*d12)))*(c12*(b12*a12)))*((((d12*b12)-(b12-a12))*((c12*c12)*(a12*(12 as int))))*(((c12-(92 as int))*(b12*b12))+((a12*a12)*(c12*(78 as int))))));
	assert(temp_12_0 == temp_12_1);

}

} // verus!