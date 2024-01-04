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
	let temp_0_0 = (((((c0*d0)-(b0+b0))*((b0*d0)*(b0*c0)))+(((d0-c0)*(b0-b0))-((a0*b0)*(d0*c0))))*((((b0*d0)*((54 as int)-a0))*((b0*c0)*(b0+b0)))*(((c0*a0)+(b0*c0))*((d0*c0)*(b0*d0)))));
	let temp_0_1 = (((((c0*d0)-(b0+b0))*((b0*d0)*(b0*c0)))+(((d0-c0)*(b0-b0))-((a0*b0)*(d0*c0))))*((((b0*d0)*((54 as int)-a0))*((c0*b0)*(b0+b0)))*(((c0*a0)+(b0*c0))*((d0*c0)*(b0*d0)))));
	assert(temp_0_0 == temp_0_1);
	let temp_1_0 = ((d1*(((b1*b1)*(c1+c1))*((c1*d1)*(b1*d1))))*((((a1*b1)-(a1*b1))+((c1*a1)*(b1-b1)))*(((d1*d1)*((23 as int)+a1))+((a1*a1)*(b1*b1)))));
	let temp_1_1 = ((d1*(((b1*b1)*(c1+c1))*((c1*d1)*(b1*d1))))*((((a1*b1)-(a1*b1))+((c1*a1)*(b1-b1)))*(((d1*d1)*((23 as int)+a1))+(((a1*a1)*b1)*b1))));
	assert(temp_1_0 == temp_1_1);
	let temp_2_0 = ((((d2*(b2*b2))*((a2+c2)*(d2*c2)))+(((d2*c2)*(d2*a2))*((a2-c2)*(b2*a2))))-((((b2*c2)*(c2+d2))*((c2+b2)+(b2*a2)))*(((c2-b2)*(a2*b2))+((a2*b2)*(d2-b2)))));
	let temp_2_1 = (((((b2*b2)*d2)*((a2+c2)*(d2*c2)))+(((d2*c2)*(d2*a2))*((a2-c2)*(b2*a2))))-((((b2*c2)*(c2+d2))*((c2+b2)+(b2*a2)))*(((c2-b2)*(a2*b2))+((a2*b2)*(d2-b2)))));
	assert(temp_2_0 == temp_2_1);
	let temp_3_0 = (((((b3*d3)*(c3*b3))*((c3*(57 as int))*(a3*b3)))*(d3*((d3-c3)-(d3*a3))))*((((53 as int)-(b3*d3))+((a3*b3)*(d3*c3)))*a3));
	let temp_3_1 = (((((b3*d3)*(c3*b3))*((c3*(57 as int))*(b3*a3)))*(d3*((d3-c3)-(d3*a3))))*((((53 as int)-(b3*d3))+((a3*b3)*(d3*c3)))*a3));
	assert(temp_3_0 == temp_3_1);
	let temp_4_0 = (((((d4+b4)*(b4*a4))*((c4*d4)*(c4*b4)))*(((d4*c4)*(d4*a4))*((c4*b4)*(a4*a4))))*((((b4*b4)*(b4*a4))*((c4*d4)-(b4-d4)))+(((c4*c4)+(c4+d4))*((b4*d4)*(a4*a4)))));
	let temp_4_1 = (((((c4*d4)*(c4*b4))*((d4+b4)*(b4*a4)))*(((d4*c4)*(d4*a4))*((c4*b4)*(a4*a4))))*((((b4*b4)*(b4*a4))*((c4*d4)-(b4-d4)))+(((c4*c4)+(c4+d4))*((b4*d4)*(a4*a4)))));
	assert(temp_4_0 == temp_4_1);
	let temp_5_0 = (((((c5*b5)+(b5*b5))*((d5-b5)*(c5*d5)))+(((c5*c5)-(c5*c5))-((d5*b5)*(c5*a5))))-((((b5+b5)*a5)+((c5*d5)*(c5*b5)))*(((a5*a5)*(b5*c5))*((b5*d5)*(c5*d5)))));
	let temp_5_1 = (((((c5*b5)+(b5*b5))*((d5-b5)*(c5*d5)))+(((c5*c5)-(c5*c5))-((d5*b5)*(c5*a5))))-((((b5+b5)*a5)+((c5*d5)*(c5*b5)))*(((b5*d5)*(c5*d5))*((a5*a5)*(b5*c5)))));
	assert(temp_5_0 == temp_5_1);
	let temp_6_0 = ((((a6*(d6+b6))-((b6*c6)*(c6*(44 as int))))-((b6*(d6*c6))*d6))*(((c6*(a6*a6))*c6)*(a6*((b6*(0 as int))*(b6*a6)))));
	let temp_6_1 = ((((a6*(d6+b6))-((b6*c6)*(c6*(44 as int))))-((b6*(d6*c6))*d6))*(((c6*(a6*a6))*c6)*(a6*((b6*(0 as int))*(b6*a6)))));
	assert(temp_6_0 == temp_6_1);
	let temp_7_0 = (((((d7*d7)+(c7+d7))*((b7*b7)*(c7+d7)))*(((d7*c7)*(b7*b7))*((a7*a7)*d7)))*((((c7*c7)*(c7*d7))*((b7*c7)-(c7+b7)))+((a7*(d7*b7))*((b7*c7)*(c7*c7)))));
	let temp_7_1 = (((((b7*b7)*(c7+d7))*((d7*d7)+(c7+d7)))*(((d7*c7)*(b7*b7))*((a7*a7)*d7)))*((((c7*c7)*(c7*d7))*((b7*c7)-(c7+b7)))+((a7*(d7*b7))*((b7*c7)*(c7*c7)))));
	assert(temp_7_0 == temp_7_1);
	let temp_8_0 = (((((b8+a8)*(a8*c8))+((c8*a8)*(c8*c8)))*c8)-((((a8*c8)-(c8*a8))*((d8*c8)*(b8*a8)))+d8));
	let temp_8_1 = (((((b8*(a8*c8))+(a8*(a8*c8)))+((c8*a8)*(c8*c8)))*c8)-((((a8*c8)-(c8*a8))*((d8*c8)*(b8*a8)))+d8));
	assert(temp_8_0 == temp_8_1);

}

} // verus!