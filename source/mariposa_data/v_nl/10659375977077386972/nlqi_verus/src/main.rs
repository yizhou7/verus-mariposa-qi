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
	let temp_0_0 = ((((b0*d0)*(d0-a0))-((d0+d0)*(b0*c0)))*(((c0*c0)*(b0*c0))-((b0+d0)*(b0*c0))));
	let temp_0_1 = ((((b0*d0)*(d0-a0))-((d0+d0)*(b0*c0)))*((c0*(c0*(b0*c0)))-((b0+d0)*(b0*c0))));
	assert(temp_0_0 == temp_0_1);
	let temp_1_0 = ((((b1+b1)*(c1*a1))-((b1*b1)+(c1*b1)))*b1);
	let temp_1_1 = ((((b1*(c1*a1))+(b1*(c1*a1)))-((b1*b1)+(c1*b1)))*b1);
	assert(temp_1_0 == temp_1_1);
	let temp_2_0 = (((((81 as int)*b2)-(a2+b2))*b2)*(((c2*(29 as int))-(c2+a2))*((c2*b2)*(b2*d2))));
	let temp_2_1 = (((((81 as int)*b2)-(a2+b2))*b2)*((((29 as int)*c2)-(c2+a2))*((c2*b2)*(b2*d2))));
	assert(temp_2_0 == temp_2_1);
	let temp_3_0 = ((((b3*b3)*(a3*d3))-((a3*b3)*(d3*b3)))+(((b3*d3)+(a3*c3))*((c3*b3)*(c3+c3))));
	let temp_3_1 = ((((b3*b3)*(a3*d3))-((a3*b3)*(d3*b3)))+(((b3*d3)+(a3*c3))*((c3*b3)*(c3+c3))));
	assert(temp_3_0 == temp_3_1);
	let temp_4_0 = ((((c4*a4)-(d4*d4))*((a4*a4)*(c4*d4)))*(b4-((d4*d4)*(c4*d4))));
	let temp_4_1 = ((((c4*a4)-(d4*d4))*((a4*a4)*(c4*d4)))*(b4-((d4*d4)*(c4*d4))));
	assert(temp_4_0 == temp_4_1);
	let temp_5_0 = ((((d5*c5)*(a5*b5))*((d5*c5)*(b5*b5)))*(((d5*a5)*(a5*b5))*((c5-b5)*d5)));
	let temp_5_1 = (((((d5*c5)*(a5*b5))*((d5*c5)*(b5*b5)))*((d5*a5)*(a5*b5)))*((c5-b5)*d5));
	assert(temp_5_0 == temp_5_1);
	let temp_6_0 = ((((c6*b6)*(c6+b6))*(a6*(a6-(38 as int))))*((a6*(c6*b6))*((b6*b6)*(c6*b6))));
	let temp_6_1 = (((((c6*b6)*c6)+((c6*b6)*b6))*(a6*(a6-(38 as int))))*((a6*(c6*b6))*((b6*b6)*(c6*b6))));
	assert(temp_6_0 == temp_6_1);
	let temp_7_0 = ((((b7+b7)*(c7*c7))*((c7*c7)*(a7*d7)))*((((95 as int)*c7)*(a7+b7))*((a7*b7)*(d7*b7))));
	let temp_7_1 = ((((b7*(c7*c7))+(b7*(c7*c7)))*((c7*c7)*(a7*d7)))*((((95 as int)*c7)*(a7+b7))*((a7*b7)*(d7*b7))));
	assert(temp_7_0 == temp_7_1);
	let temp_8_0 = ((((d8*a8)*(d8+c8))*a8)*((b8*(a8*c8))-((b8-a8)*(a8+b8))));
	let temp_8_1 = (((d8*(a8*(d8+c8)))*a8)*((b8*(a8*c8))-((b8-a8)*(a8+b8))));
	assert(temp_8_0 == temp_8_1);
	let temp_9_0 = (((d9*(c9*d9))*((b9*c9)*(a9+d9)))*(((d9*d9)*(c9*d9))*((b9*d9)-(d9+c9))));
	let temp_9_1 = ((((d9*(c9*d9))*(b9*c9))*(a9+d9))*(((d9*d9)*(c9*d9))*((b9*d9)-(d9+c9))));
	assert(temp_9_0 == temp_9_1);
	let temp_10_0 = ((((a10*c10)*(d10*d10))*((d10-d10)*(a10*d10)))*(((c10*b10)-(a10+d10))*((d10+b10)*(a10*a10))));
	let temp_10_1 = ((((d10-d10)*(a10*d10))*((a10*c10)*(d10*d10)))*(((c10*b10)-(a10+d10))*((d10+b10)*(a10*a10))));
	assert(temp_10_0 == temp_10_1);
	let temp_11_0 = ((((a11*d11)*(b11-b11))*(d11*(b11*d11)))*(((a11*a11)*(b11*d11))*((a11*c11)*(c11*c11))));
	let temp_11_1 = (((d11*(b11*d11))*((a11*d11)*(b11-b11)))*(((a11*a11)*(b11*d11))*((a11*c11)*(c11*c11))));
	assert(temp_11_0 == temp_11_1);
	let temp_12_0 = (((a12*(b12*d12))*((b12*b12)*(b12*c12)))+(((c12*(44 as int))*(c12*a12))*((b12*b12)*(b12*a12))));
	let temp_12_1 = ((((b12*b12)*(b12*c12))*(a12*(b12*d12)))+(((c12*(44 as int))*(c12*a12))*((b12*b12)*(b12*a12))));
	assert(temp_12_0 == temp_12_1);
	let temp_13_0 = ((((a13-c13)*d13)*((d13*a13)*(c13*c13)))+(((d13-c13)*(b13+a13))+((a13*c13)*(d13*a13))));
	let temp_13_1 = ((((a13-c13)*d13)*((d13*a13)*(c13*c13)))+(((d13-c13)*(b13+a13))+((c13*a13)*(d13*a13))));
	assert(temp_13_0 == temp_13_1);
	let temp_14_0 = ((b14+((d14*b14)*(a14+a14)))*((a14-(b14*a14))*((c14*b14)+(a14*d14))));
	let temp_14_1 = ((b14+((d14*b14)*(a14+a14)))*(((c14*b14)+(a14*d14))*(a14-(b14*a14))));
	assert(temp_14_0 == temp_14_1);
	let temp_15_0 = ((((d15*c15)*(c15+b15))*((b15*b15)*(c15+a15)))*(((b15*a15)+(c15*c15))*((b15+c15)*(d15+b15))));
	let temp_15_1 = ((((d15*c15)*(c15+b15))*((b15*b15)*(c15+a15)))*(((b15*a15)+(c15*c15))*((d15+b15)*(b15+c15))));
	assert(temp_15_0 == temp_15_1);
	let temp_16_0 = (((b16*(b16*c16))*a16)*(b16*((b16*d16)*(b16*d16))));
	let temp_16_1 = ((b16*((b16*d16)*(b16*d16)))*((b16*(b16*c16))*a16));
	assert(temp_16_0 == temp_16_1);
	let temp_17_0 = ((((d17*c17)*(d17*a17))*d17)*(d17*((b17*d17)*(a17*c17))));
	let temp_17_1 = ((((d17*c17)*(d17*a17))*d17)*(d17*((a17*c17)*(b17*d17))));
	assert(temp_17_0 == temp_17_1);
	let temp_18_0 = ((((d18*b18)*(c18*c18))+(d18*(c18*d18)))*((c18*(c18-c18))*((a18*c18)*(b18-b18))));
	let temp_18_1 = ((((d18*b18)*(c18*c18))+((d18*c18)*d18))*((c18*(c18-c18))*((a18*c18)*(b18-b18))));
	assert(temp_18_0 == temp_18_1);
	let temp_19_0 = ((((c19+d19)*(b19*d19))*((b19*d19)+(b19*d19)))*(((d19*d19)*((84 as int)*b19))+((a19*c19)*(a19+c19))));
	let temp_19_1 = ((((b19*d19)+(b19*d19))*((c19+d19)*(b19*d19)))*(((d19*d19)*((84 as int)*b19))+((a19*c19)*(a19+c19))));
	assert(temp_19_0 == temp_19_1);
	let temp_20_0 = ((((c20*a20)*(a20*d20))*((c20*d20)*d20))*(((b20-c20)*(a20*a20))*((b20*c20)*b20)));
	let temp_20_1 = ((((c20*d20)*d20)*((c20*a20)*(a20*d20)))*(((b20-c20)*(a20*a20))*((b20*c20)*b20)));
	assert(temp_20_0 == temp_20_1);
	let temp_21_0 = ((((b21-b21)*(b21*a21))-((b21*b21)*(c21*a21)))*(c21*((d21*a21)*(c21*c21))));
	let temp_21_1 = ((((b21*(b21*a21))-(b21*(b21*a21)))-((b21*b21)*(c21*a21)))*(c21*((d21*a21)*(c21*c21))));
	assert(temp_21_0 == temp_21_1);
	let temp_22_0 = ((((c22-c22)*(a22*d22))+((a22*d22)*(a22*c22)))*(((a22*a22)*(c22*c22))*((c22*b22)*(a22*c22))));
	let temp_22_1 = ((((a22*d22)*(c22-c22))+((a22*d22)*(a22*c22)))*(((a22*a22)*(c22*c22))*((c22*b22)*(a22*c22))));
	assert(temp_22_0 == temp_22_1);
	let temp_23_0 = ((((d23*c23)*((75 as int)*a23))*((d23*d23)+(b23*b23)))*(((a23*b23)*(d23*a23))*((d23*d23)-(b23*c23))));
	let temp_23_1 = ((((c23*d23)*((75 as int)*a23))*((d23*d23)+(b23*b23)))*(((a23*b23)*(d23*a23))*((d23*d23)-(b23*c23))));
	assert(temp_23_0 == temp_23_1);
	let temp_24_0 = ((((a24*c24)*(b24*a24))-c24)*(((d24*d24)*(d24*c24))*((a24*b24)*(c24*c24))));
	let temp_24_1 = ((((a24*c24)*(b24*a24))-c24)*(((d24*d24)*(c24*d24))*((a24*b24)*(c24*c24))));
	assert(temp_24_0 == temp_24_1);
	let temp_25_0 = ((a25*(a25*(b25*b25)))*(((b25*b25)*(d25*a25))*((b25-a25)*(d25*a25))));
	let temp_25_1 = ((a25*(a25*(b25*b25)))*(((b25*b25)*(d25*a25))*((b25-a25)*(d25*a25))));
	assert(temp_25_0 == temp_25_1);
	let temp_26_0 = ((((b26*a26)*(b26*a26))*((b26*(66 as int))*(d26*b26)))+((c26*(b26*b26))*((a26*c26)*(c26-b26))));
	let temp_26_1 = ((((b26*a26)*(b26*a26))*((d26*b26)*(b26*(66 as int))))+((c26*(b26*b26))*((a26*c26)*(c26-b26))));
	assert(temp_26_0 == temp_26_1);

}

} // verus!