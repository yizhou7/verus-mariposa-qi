use builtin_macros::*;
use builtin::*;
use vstd::calc_macro::*;
use crate::nl_basics::*;
verus! {

pub proof fn lemma_test(a: int, b: int, c: int) by (nonlinear_arith) {
		let temp_0 = (((((c*a)*(b*b))*(((94 as int)*a)*(c*a)))+(((a*c)+(a*c))*((a*b)*(a*a))))*((((b*b)*c)*((b+b)-(c*b)))*((c*(c*b))*((b-b)*(c*a)))));
		let temp_1 = (((((c*a)*(b*b))*(((94 as int)*a)*(c*a)))+(((a*c)+(a*c))*((a*b)*(a*a))))*((((b*b)*c)*((b+b)-(c*b)))*((c*(c*b))*((b-b)*(c*a)))));
		let temp_2 = (((((c*a)*(b*b))*(((94 as int)*a)*(c*a)))+(((a*c)+(a*c))*((a*b)*(a*a))))*(((((b*b)*c)*(b+b))-(((b*b)*c)*(c*b)))*((c*(c*b))*((b-b)*(c*a)))));
		let temp_3 = (((((c*a)*(b*b))*(((94 as int)*a)*(c*a)))+(((a*c)+(a*c))*(a*(b*(a*a)))))*(((((b*b)*c)*(b+b))-(((b*b)*c)*(c*b)))*((c*(c*b))*((b-b)*(c*a)))));
		let temp_4 = (((((c*a)*(b*b))*(((94 as int)*a)*(c*a)))+(((a*c)+(a*c))*(a*(b*(a*a)))))*(((((b*b)*c)*(b+b))-(((b*b)*c)*(c*b)))*((c*(c*b))*((b*(c*a))-(b*(c*a))))));
		let temp_5 = (((((c*a)*(b*b))*(((94 as int)*a)*(c*a)))*(((((b*b)*c)*(b+b))-(((b*b)*c)*(c*b)))*((c*(c*b))*((b*(c*a))-(b*(c*a))))))+((((a*c)+(a*c))*(a*(b*(a*a))))*(((((b*b)*c)*(b+b))-(((b*b)*c)*(c*b)))*((c*(c*b))*((b*(c*a))-(b*(c*a)))))));
		let temp_6 = (((((c*a)*(b*b))*(((94 as int)*a)*(c*a)))*(((((b*b)*c)*(b+b))*((c*(c*b))*((b*(c*a))-(b*(c*a)))))-((((b*b)*c)*(c*b))*((c*(c*b))*((b*(c*a))-(b*(c*a)))))))+((((a*c)+(a*c))*(a*(b*(a*a))))*(((((b*b)*c)*(b+b))*((c*(c*b))*((b*(c*a))-(b*(c*a)))))-((((b*b)*c)*(c*b))*((c*(c*b))*((b*(c*a))-(b*(c*a))))))));
		let temp_7 = (((((c*a)*(b*b))*(((94 as int)*a)*(c*a)))+(((a*c)+(a*c))*(a*(b*(a*a)))))*(((((b*b)*c)*(b+b))*((c*(c*b))*((b*(c*a))-(b*(c*a)))))-((((b*b)*c)*(c*b))*((c*(c*b))*((b*(c*a))-(b*(c*a)))))));
		let temp_8 = (((((c*a)*(b*b))*(((94 as int)*a)*(c*a)))+(((a*c)+(a*c))*(a*(b*(a*a)))))*(((((b*b)*c)*(b+b))*(((c*(c*b))*(b*(c*a)))-((c*(c*b))*(b*(c*a)))))-((((b*b)*c)*(c*b))*(((c*(c*b))*(b*(c*a)))-((c*(c*b))*(b*(c*a)))))));
		let temp_9 = (((((c*a)*(b*b))*(((94 as int)*a)*(c*a)))+((a*(c+c))*(a*(b*(a*a)))))*(((((b*b)*c)*(b+b))*(((c*(c*b))*(b*(c*a)))-((c*(c*b))*(b*(c*a)))))-((((b*b)*c)*(c*b))*(((c*(c*b))*(b*(c*a)))-((c*(c*b))*(b*(c*a)))))));
		let temp_10 = (((((c*a)*(b*b))*(((94 as int)*a)*(c*a)))+((a*(c+c))*(a*(b*(a*a)))))*((((b*(b*c))*(b+b))*(((c*(c*b))*(b*(c*a)))-((c*(c*b))*(b*(c*a)))))-(((b*(b*c))*(c*b))*(((c*(c*b))*(b*(c*a)))-((c*(c*b))*(b*(c*a)))))));
		let temp_11 = (((((c*a)*(b*b))*(((94 as int)*a)*(c*a)))+((a*(c+c))*(a*(b*(a*a)))))*((((b*(b*c))*(b+b))*((c*(c*b))*((b*(c*a))-(b*(c*a)))))-(((b*(b*c))*(c*b))*((c*(c*b))*((b*(c*a))-(b*(c*a)))))));
		assert(temp_0 == temp_1) by 
			{}	// 0
		assert(temp_1 == temp_2) by 
			{}	// 1
		assert(temp_2 == temp_3) by 
			{}	// 2
		assert(temp_3 == temp_4) by 
			{}	// 3
		assert(temp_4 == temp_5) by 
			{}	// 4
		assert(temp_5 == temp_6) by 
			{}	// 5
		assert(temp_6 == temp_7) by 
			{}	// 6
		assert(temp_7 == temp_8) by 
			{}	// 7
		assert(temp_8 == temp_9) by 
			{}	// 8
		assert(temp_9 == temp_10) by 
			{}	// 9
		assert(temp_10 == temp_11) by 
			{}	// 10
}
} // verus!