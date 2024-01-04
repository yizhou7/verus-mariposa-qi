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
	let temp_0_0 = (((((c0*d0)*(c0*d0))*((a0*b0)*(b0*a0)))+((a0*(a0+a0))*((d0*a0)*(d0*a0))))*((((b0*(67 as int))*(d0*a0))*((d0*b0)*(b0*b0)))-c0));
	let temp_0_1 = (((((c0*d0)*(c0*d0))*((a0*b0)*(b0*a0)))+(((d0*a0)*(d0*a0))*(a0*(a0+a0))))*((((b0*(67 as int))*(d0*a0))*((d0*b0)*(b0*b0)))-c0));
	assert(temp_0_0 == temp_0_1);
	let temp_1_0 = (((((a1*d1)*(d1*b1))*(d1*(d1*d1)))*((b1*(d1-c1))*((d1*a1)+(a1*a1))))*((((a1*b1)-(a1*b1))*(((91 as int)*a1)*(c1*b1)))*(c1*((d1*d1)*(d1*c1)))));
	let temp_1_1 = (((((a1*d1)*(d1*b1))*(d1*(d1*d1)))*((b1*(d1-c1))*((d1*a1)+(a1*a1))))*((((a1*b1)-(a1*b1))*(((91 as int)*a1)*(c1*b1)))*(c1*((d1*d1)*(c1*d1)))));
	assert(temp_1_0 == temp_1_1);
	let temp_2_0 = ((((a2*(a2*d2))*((b2*a2)*(a2*b2)))-(a2+((b2*a2)*(b2*b2))))*((c2*(d2*(c2*b2)))-(((c2+c2)*(d2*a2))*(((44 as int)-a2)*(d2*b2)))));
	let temp_2_1 = ((((a2*(a2*d2))*((b2*a2)*(a2*b2)))-(a2+((b2*a2)*(b2*b2))))*((c2*((c2*b2)*d2))-(((c2+c2)*(d2*a2))*(((44 as int)-a2)*(d2*b2)))));
	assert(temp_2_0 == temp_2_1);
	let temp_3_0 = (((((d3*b3)*(c3*c3))*a3)*(b3*((d3*a3)*(a3-a3))))*((((a3*b3)*(b3*c3))*((a3+c3)*(a3+d3)))*((((69 as int)*a3)*(a3*d3))+((a3*c3)+(a3*d3)))));
	let temp_3_1 = (((((c3*c3)*(d3*b3))*a3)*(b3*((d3*a3)*(a3-a3))))*((((a3*b3)*(b3*c3))*((a3+c3)*(a3+d3)))*((((69 as int)*a3)*(a3*d3))+((a3*c3)+(a3*d3)))));
	assert(temp_3_0 == temp_3_1);
	let temp_4_0 = (((((b4*b4)-(a4*c4))-(a4*(a4*b4)))*(((c4*b4)*(d4*b4))*((a4*a4)*b4)))*((((c4*d4)-(d4*a4))*((b4*c4)*(b4*c4)))*(((b4*b4)*(d4*c4))+((c4*a4)*(a4*c4)))));
	let temp_4_1 = (((((b4*b4)-(a4*c4))-(a4*(a4*b4)))*(((c4*b4)*(d4*b4))*((a4*a4)*b4)))*((((c4*d4)-(d4*a4))*((b4*c4)*(b4*c4)))*(((b4*b4)*(d4*c4))+((c4*a4)*(a4*c4)))));
	assert(temp_4_0 == temp_4_1);
	let temp_5_0 = (((((d5*c5)*(b5*a5))*a5)*(((d5*a5)*(c5-b5))*((b5*b5)*(a5*d5))))*((((c5*c5)+(a5*d5))*((c5*b5)*(a5-a5)))*(((a5+c5)*(d5*a5))*((c5*b5)+(d5*c5)))));
	let temp_5_1 = (((((d5*c5)*(b5*a5))*a5)*(((d5*a5)*(c5-b5))*((b5*b5)*(a5*d5))))*((((c5*c5)+(a5*d5))*((a5-a5)*(c5*b5)))*(((a5+c5)*(d5*a5))*((c5*b5)+(d5*c5)))));
	assert(temp_5_0 == temp_5_1);
	let temp_6_0 = (((((b6*d6)*(d6*a6))*((c6*b6)*(b6*d6)))*(((c6*b6)*(b6*a6))*((b6*d6)-(c6+a6))))+((((b6*c6)+(a6*c6))*((b6+d6)*(d6*d6)))*(((a6*a6)*c6)*((b6*d6)*b6))));
	let temp_6_1 = (((((b6*d6)*(d6*a6))*((c6*b6)*(b6*d6)))*(((c6*b6)*(b6*a6))*((b6*d6)-(c6+a6))))+((((b6*c6)+(a6*c6))*((b6+d6)*(d6*d6)))*((((a6*a6)*c6)*(b6*d6))*b6)));
	assert(temp_6_0 == temp_6_1);
	let temp_7_0 = ((((c7*(c7*d7))*((b7-d7)*(d7*b7)))-(((b7*c7)*(b7+d7))*((d7*a7)*(d7*d7))))+((((a7*c7)*(d7*b7))-((d7*d7)*(a7*b7)))*a7));
	let temp_7_1 = ((((c7*(c7*d7))*((b7-d7)*(b7*d7)))-(((b7*c7)*(b7+d7))*((d7*a7)*(d7*d7))))+((((a7*c7)*(d7*b7))-((d7*d7)*(a7*b7)))*a7));
	assert(temp_7_0 == temp_7_1);
	let temp_8_0 = ((((c8*(d8*c8))*((a8*b8)*(b8*b8)))*(((a8*b8)*(d8+d8))-((a8*a8)*(a8*c8))))*((((a8*d8)-(c8*b8))+d8)*(((a8*b8)*(a8*c8))*((d8*b8)-(b8*d8)))));
	let temp_8_1 = ((((c8*(d8*c8))*((a8*b8)*(b8*b8)))*(((b8*a8)*(d8+d8))-((a8*a8)*(a8*c8))))*((((a8*d8)-(c8*b8))+d8)*(((a8*b8)*(a8*c8))*((d8*b8)-(b8*d8)))));
	assert(temp_8_0 == temp_8_1);
	let temp_9_0 = (((((b9*a9)*(c9*c9))*((a9*b9)*(a9*c9)))*(((a9*d9)*(a9-d9))*(c9*(d9*b9))))*(((c9*(c9*b9))*((b9*d9)+(a9+c9)))*(((a9*b9)+(b9*(33 as int)))*((a9*a9)*(a9-a9)))));
	let temp_9_1 = (((((a9*b9)*(c9*c9))*((a9*b9)*(a9*c9)))*(((a9*d9)*(a9-d9))*(c9*(d9*b9))))*(((c9*(c9*b9))*((b9*d9)+(a9+c9)))*(((a9*b9)+(b9*(33 as int)))*((a9*a9)*(a9-a9)))));
	assert(temp_9_0 == temp_9_1);

}

} // verus!