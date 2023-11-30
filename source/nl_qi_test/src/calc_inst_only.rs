use builtin_macros::*;
use builtin::*;
use vstd::calc_macro::*;
use crate::nl_basics::*;
verus! {

pub proof fn lemma_test(a: int, b: int, c: int) {
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
		let temp_12 = (((((c*a)*(b*b))*(((94 as int)*a)*(c*a)))+((a*(c+c))*(a*(b*(a*a)))))*(((((b*b)*c)*(b+b))*((c*(c*b))*((b*(c*a))-(b*(c*a)))))-((((b*b)*c)*(c*b))*((c*(c*b))*((b*(c*a))-(b*(c*a)))))));
		let temp_13 = (((((c*a)*(b*b))*(((94 as int)*a)*(c*a)))+((a*(c+c))*(a*(b*(a*a)))))*(((((b*b)*c)*(b+b))*((c*(c*b))*(((b*c)*a)-(b*(c*a)))))-((((b*b)*c)*(c*b))*((c*(c*b))*(((b*c)*a)-(b*(c*a)))))));
		let temp_14 = (((((c*a)*(b*b))*(((94 as int)*a)*(c*a)))+((a*(c+c))*(a*(b*(a*a)))))*(((((b*b)*c)*(b+b))*((c*(c*b))*(((b*c)*a)-(b*(c*a)))))-(((((b*b)*c)*(c*b))*(c*(c*b)))*(((b*c)*a)-(b*(c*a))))));
		let temp_15 = (((((c*a)*(b*b))*(((94 as int)*a)*(c*a)))+((a*(c+c))*((a*b)*(a*a))))*(((((b*b)*c)*(b+b))*((c*(c*b))*(((b*c)*a)-(b*(c*a)))))-(((((b*b)*c)*(c*b))*(c*(c*b)))*(((b*c)*a)-(b*(c*a))))));
		let temp_16 = (((((c*a)*(b*b))*(((94 as int)*a)*(c*a)))+(((a*c)+(a*c))*((a*b)*(a*a))))*(((((b*b)*c)*(b+b))*((c*(c*b))*(((b*c)*a)-(b*(c*a)))))-(((((b*b)*c)*(c*b))*(c*(c*b)))*(((b*c)*a)-(b*(c*a))))));
		let temp_17 = (((((c*a)*(b*b))*(((94 as int)*a)*(c*a)))+(((a*c)+(a*c))*((a*b)*(a*a))))*((((b*b)*c)*((b+b)*((c*(c*b))*(((b*c)*a)-(b*(c*a))))))-(((((b*b)*c)*(c*b))*(c*(c*b)))*(((b*c)*a)-(b*(c*a))))));
		let temp_18 = (((((c*a)*(b*b))*(((94 as int)*a)*(c*a)))+(((a*c)+(a*c))*((a*b)*(a*a))))*((((b*b)*c)*((b+b)*((c*(c*b))*(((b*c)*a)-(b*(c*a))))))-((((((b*b)*c)*(c*b))*(c*(c*b)))*((b*c)*a))-(((((b*b)*c)*(c*b))*(c*(c*b)))*(b*(c*a))))));
		let temp_19 = (((((c*a)*(b*b))*(((94 as int)*a)*(c*a)))+(((a*c)+(a*c))*((a*b)*(a*a))))*((((b*b)*c)*(((b+b)*(c*(c*b)))*(((b*c)*a)-(b*(c*a)))))-((((((b*b)*c)*(c*b))*(c*(c*b)))*((b*c)*a))-(((((b*b)*c)*(c*b))*(c*(c*b)))*(b*(c*a))))));
		let temp_20 = (((((c*a)*(b*b))*(((94 as int)*a)*(c*a)))+(((a+a)*c)*((a*b)*(a*a))))*((((b*b)*c)*(((b+b)*(c*(c*b)))*(((b*c)*a)-(b*(c*a)))))-((((((b*b)*c)*(c*b))*(c*(c*b)))*((b*c)*a))-(((((b*b)*c)*(c*b))*(c*(c*b)))*(b*(c*a))))));
		assert(temp_0 == temp_1) by 
			{lemma_mul_is_commutative(a, a);}	// 0
		assert(temp_1 == temp_2) by 
			{lemma_mul_is_distributive(((b*b)*c), (b+b), (c*b));}	// 1
		assert(temp_2 == temp_3) by 
			{lemma_mul_is_associative(a, b, (a*a));}	// 2
		assert(temp_3 == temp_4) by 
			{lemma_mul_is_distributive(b, b, (c*a));}	// 3
		assert(temp_4 == temp_5) by 
			{lemma_mul_is_distributive((((c*a)*(b*b))*(((94 as int)*a)*(c*a))), (((a*c)+(a*c))*(a*(b*(a*a)))), (((((b*b)*c)*(b+b))-(((b*b)*c)*(c*b)))*((c*(c*b))*((b*(c*a))-(b*(c*a))))));}	// 4
		assert(temp_5 == temp_6) by 
			{lemma_mul_is_distributive((((b*b)*c)*(b+b)), (((b*b)*c)*(c*b)), ((c*(c*b))*((b*(c*a))-(b*(c*a)))));}	// 5
		assert(temp_6 == temp_7) by 
			{lemma_mul_is_distributive((((c*a)*(b*b))*(((94 as int)*a)*(c*a))), (((a*c)+(a*c))*(a*(b*(a*a)))), (((((b*b)*c)*(b+b))*((c*(c*b))*((b*(c*a))-(b*(c*a)))))-((((b*b)*c)*(c*b))*((c*(c*b))*((b*(c*a))-(b*(c*a)))))));}	// 6
		assert(temp_7 == temp_8) by 
			{lemma_mul_is_distributive((c*(c*b)), (b*(c*a)), (b*(c*a)));}	// 7
		assert(temp_8 == temp_9) by 
			{lemma_mul_is_distributive(a, c, c);}	// 8
		assert(temp_9 == temp_10) by 
			{lemma_mul_is_associative(b, b, c);}	// 9
		assert(temp_10 == temp_11) by 
			{lemma_mul_is_distributive((c*(c*b)), (b*(c*a)), (b*(c*a)));}	// 10
		assert(temp_11 == temp_12) by 
			{lemma_mul_is_associative(b, b, c);}	// 11
		assert(temp_12 == temp_13) by 
			{lemma_mul_is_associative(b, c, a);}	// 12
		assert(temp_13 == temp_14) by 
			{lemma_mul_is_associative((((b*b)*c)*(c*b)), (c*(c*b)), (((b*c)*a)-(b*(c*a))));}	// 13
		assert(temp_14 == temp_15) by 
			{lemma_mul_is_associative(a, b, (a*a));}	// 14
		assert(temp_15 == temp_16) by 
			{lemma_mul_is_distributive(a, c, c);}	// 15
		assert(temp_16 == temp_17) by 
			{lemma_mul_is_associative(((b*b)*c), (b+b), ((c*(c*b))*(((b*c)*a)-(b*(c*a)))));}	// 16
		assert(temp_17 == temp_18) by 
			{lemma_mul_is_distributive(((((b*b)*c)*(c*b))*(c*(c*b))), ((b*c)*a), (b*(c*a)));}	// 17
		assert(temp_18 == temp_19) by 
			{lemma_mul_is_associative((b+b), (c*(c*b)), (((b*c)*a)-(b*(c*a))));}	// 18
		assert(temp_19 == temp_20) by 
			{lemma_mul_is_distributive(a, a, c);}	// 19
}
} // verus!