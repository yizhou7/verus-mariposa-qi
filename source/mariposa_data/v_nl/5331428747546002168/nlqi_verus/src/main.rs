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
	let temp_0_0 = ((((d0*a0)*(d0*d0))*((b0*d0)*(b0*b0)))*(((b0*d0)*(c0*d0))*((a0*c0)*(d0-b0))));
	let temp_0_1 = ((((b0*d0)*(c0*d0))*((a0*c0)*(d0-b0)))*(((d0*a0)*(d0*d0))*((b0*d0)*(b0*b0))));
	assert(temp_0_0 == temp_0_1);
	let temp_1_0 = (((c1*(b1-c1))*((c1-b1)+(d1*c1)))*(((c1*a1)*(c1*c1))*((b1*(50 as int))*((86 as int)*c1))));
	let temp_1_1 = ((((c1*a1)*(c1*c1))*((b1*(50 as int))*((86 as int)*c1)))*((c1*(b1-c1))*((c1-b1)+(d1*c1))));
	assert(temp_1_0 == temp_1_1);
	let temp_2_0 = ((((c2*b2)*(c2*a2))*((b2-b2)-(b2*c2)))*(((c2*c2)*(d2*d2))*(c2*(a2*a2))));
	let temp_2_1 = ((((c2*b2)*(c2*a2))*((b2-b2)-(c2*b2)))*(((c2*c2)*(d2*d2))*(c2*(a2*a2))));
	assert(temp_2_0 == temp_2_1);
	let temp_3_0 = ((((b3*b3)*(a3*c3))*((c3*b3)-(d3-d3)))+(((b3*b3)*(c3*c3))-((d3*d3)*(c3-d3))));
	let temp_3_1 = ((((b3*b3)*(a3*c3))*((c3*b3)-(d3-d3)))+(((b3*b3)*(c3*c3))-((d3*d3)*(c3-d3))));
	assert(temp_3_0 == temp_3_1);
	let temp_4_0 = ((((a4+c4)-(c4*d4))*(b4*(a4*b4)))*(((d4*d4)*(a4-d4))*((c4*d4)*(b4*c4))));
	let temp_4_1 = (((b4*(a4*b4))*((a4+c4)-(c4*d4)))*(((d4*d4)*(a4-d4))*((c4*d4)*(b4*c4))));
	assert(temp_4_0 == temp_4_1);
	let temp_5_0 = (a5+(((c5*d5)*(a5*a5))*((c5*d5)*(d5+a5))));
	let temp_5_1 = (a5+((c5*(d5*(a5*a5)))*((c5*d5)*(d5+a5))));
	assert(temp_5_0 == temp_5_1);
	let temp_6_0 = ((((d6*d6)*(a6*b6))*((b6+c6)*c6))*(((b6*b6)*(a6*c6))*((b6*d6)*(c6*b6))));
	let temp_6_1 = ((((d6*d6)*(a6*b6))*((b6+c6)*c6))*(((b6*b6)*(a6*c6))*((c6*b6)*(b6*d6))));
	assert(temp_6_0 == temp_6_1);
	let temp_7_0 = ((((c7*d7)*(d7+b7))*((a7*(69 as int))+(b7+(9 as int))))*(((b7*d7)*(b7*b7))+((d7*c7)*(a7*a7))));
	let temp_7_1 = ((((a7*(69 as int))+(b7+(9 as int)))*((c7*d7)*(d7+b7)))*(((b7*d7)*(b7*b7))+((d7*c7)*(a7*a7))));
	assert(temp_7_0 == temp_7_1);
	let temp_8_0 = ((((b8*c8)*(c8*c8))*((a8*d8)*(b8*b8)))*(((a8*d8)*(b8+d8))-((c8*a8)*(c8+a8))));
	let temp_8_1 = ((((c8*c8)*(b8*c8))*((a8*d8)*(b8*b8)))*(((a8*d8)*(b8+d8))-((c8*a8)*(c8+a8))));
	assert(temp_8_0 == temp_8_1);
	let temp_9_0 = ((((b9*a9)*(c9-d9))*((c9*a9)*(d9*b9)))*(((b9*b9)*(d9*(74 as int)))-c9));
	let temp_9_1 = ((((b9*a9)*(c9-d9))*((c9*a9)*(d9*b9)))*(((b9*b9)*((74 as int)*d9))-c9));
	assert(temp_9_0 == temp_9_1);
	let temp_10_0 = ((((a10*d10)*(d10-a10))+((b10*d10)*(a10*b10)))*(((c10*a10)*(b10*d10))*((a10*c10)*(d10*d10))));
	let temp_10_1 = ((((a10*d10)*(d10-a10))+((b10*d10)*(a10*b10)))*(((c10*a10)*(b10*d10))*((d10*d10)*(a10*c10))));
	assert(temp_10_0 == temp_10_1);
	let temp_11_0 = ((((a11-a11)*(c11+a11))*((a11*c11)*(c11-d11)))+(((d11*b11)+(c11*b11))*((c11*b11)-(c11*d11))));
	let temp_11_1 = ((((a11-a11)*(c11+a11))*((a11*c11)*(c11-d11)))+(((d11*b11)+(c11*b11))*(c11*(b11-d11))));
	assert(temp_11_0 == temp_11_1);
	let temp_12_0 = ((((b12*a12)*(d12*b12))*((c12*b12)*(c12*c12)))*(((b12*c12)+(a12*c12))*((d12*c12)*(b12*a12))));
	let temp_12_1 = (((b12*a12)*((d12*b12)*((c12*b12)*(c12*c12))))*(((b12*c12)+(a12*c12))*((d12*c12)*(b12*a12))));
	assert(temp_12_0 == temp_12_1);
	let temp_13_0 = ((((a13*c13)*(d13*c13))-((a13*d13)*(d13*d13)))+(((d13*b13)*c13)*((a13*a13)*(c13*b13))));
	let temp_13_1 = ((((a13*c13)*(d13*c13))-((a13*d13)*(d13*d13)))+(((d13*b13)*c13)*((a13*a13)*(b13*c13))));
	assert(temp_13_0 == temp_13_1);
	let temp_14_0 = ((((c14*c14)*(b14*b14))*((a14*c14)*(b14*b14)))*(((c14*d14)*a14)*((a14*d14)*(a14-c14))));
	let temp_14_1 = ((((c14*c14)*(b14*b14))*((a14*c14)*(b14*b14)))*((a14*(c14*d14))*((a14*d14)*(a14-c14))));
	assert(temp_14_0 == temp_14_1);
	let temp_15_0 = ((((c15*a15)+(c15+b15))*((c15*c15)+(b15*a15)))*(((d15*(24 as int))+(c15*a15))*((c15*b15)*(a15*a15))));
	let temp_15_1 = ((((c15*a15)+(c15+b15))*((c15*c15)+(b15*a15)))*(((c15*b15)*(a15*a15))*((d15*(24 as int))+(c15*a15))));
	assert(temp_15_0 == temp_15_1);
	let temp_16_0 = (((((97 as int)+c16)*(a16*a16))*((a16-a16)+(c16*c16)))*(((c16*(29 as int))+(c16*c16))*((d16+b16)-(b16*d16))));
	let temp_16_1 = (((((97 as int)+c16)*(a16*a16))*((a16-a16)+(c16*c16)))*(((c16*(29 as int))+(c16*c16))*((d16+b16)-(b16*d16))));
	assert(temp_16_0 == temp_16_1);
	let temp_17_0 = ((((b17*d17)*(a17*a17))*((a17*a17)*(a17*c17)))*(((a17*c17)*(a17+b17))*((c17*a17)+(b17*c17))));
	let temp_17_1 = ((((b17*d17)*(a17*a17))*(a17*(a17*(a17*c17))))*(((a17*c17)*(a17+b17))*((c17*a17)+(b17*c17))));
	assert(temp_17_0 == temp_17_1);
	let temp_18_0 = ((((a18-d18)*(a18*d18))*((d18*b18)*(a18*a18)))*(((a18*a18)*c18)*((c18*d18)*(b18*d18))));
	let temp_18_1 = ((((a18-d18)*(a18*d18))*((d18*b18)*(a18*a18)))*(((a18*a18)*c18)*((c18*d18)*(b18*d18))));
	assert(temp_18_0 == temp_18_1);
	let temp_19_0 = (c19+(((c19*c19)*(a19+b19))*((b19*c19)*(b19*d19))));
	let temp_19_1 = (c19+(((c19*c19)*(a19+b19))*((c19*b19)*(b19*d19))));
	assert(temp_19_0 == temp_19_1);
	let temp_20_0 = ((b20*b20)*(((b20*c20)*(b20*d20))*((c20-c20)*(c20*d20))));
	let temp_20_1 = ((b20*b20)*(((b20*c20)*(b20*d20))*((c20*d20)*(c20-c20))));
	assert(temp_20_0 == temp_20_1);
	let temp_21_0 = ((((d21*a21)-(d21*b21))*((b21*c21)*(d21*a21)))*(((c21*c21)*(b21*d21))+((a21*(5 as int))*(a21*d21))));
	let temp_21_1 = ((((d21*a21)-(d21*b21))*((b21*c21)*(d21*a21)))*(((b21*d21)*(c21*c21))+((a21*(5 as int))*(a21*d21))));
	assert(temp_21_0 == temp_21_1);
	let temp_22_0 = (((((24 as int)*c22)*(a22*b22))+((c22*d22)*(c22*c22)))*(((a22*c22)-(c22*d22))+((b22-b22)*(a22*b22))));
	let temp_22_1 = (((((24 as int)*c22)*(a22*b22))+((c22*d22)*(c22*c22)))*(((a22*c22)-(c22*d22))+((b22*(a22*b22))-(b22*(a22*b22)))));
	assert(temp_22_0 == temp_22_1);
	let temp_23_0 = ((((d23*c23)*(c23*b23))*(b23*(b23*c23)))*(((c23*c23)*(c23*b23))*((d23-d23)-(a23-b23))));
	let temp_23_1 = ((((d23*c23)*(c23*b23))*(b23*(b23*c23)))*((c23*c23)*((c23*b23)*((d23-d23)-(a23-b23)))));
	assert(temp_23_0 == temp_23_1);

}

} // verus!