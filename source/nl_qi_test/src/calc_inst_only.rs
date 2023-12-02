use builtin_macros::*;
use builtin::*;
use crate::nl_basics::*;
verus! {

use vstd::calc_macro::*;
pub proof fn lemma_test(a: int, b: int, c: int, d: int)
{
	let temp_0_0 = ((((b*c)+((a*d)*((c*((((c*b)*a)*c)*(((b*a)*(d*c))*a)))*((b*(d*b))*((b*((b-d)*c))*(((d*b)*a)*((b*b)-(d+a))))))))*a)*(b+c));
	let temp_0_2 = ((((b*c)+((a*d)*((c*((((c*b)*a)*c)*(((b*a)*(d*c))*a)))*(((b*d)*b)*((b*((b-d)*c))*((((d*b)*a)*(b*b))-(((d*b)*a)*(d+a))))))))*a)*(b+c));
	calc !{
		(==)
		temp_0_0;
					{lemma_mul_is_associative(b, d, b);
			lemma_mul_is_distributive(((d*b)*a), (b*b), (d+a));}// 2
		temp_0_2;
	}
	let temp_1_0 = (((c*((c*a)*d))+((b*(b*(c-(((d*(c*a))*d)*b))))*(((((((a*a)-(b*a))*((a*a)*(b+d)))*(((b+c)*a)*((a*a)*(b-d))))*(a*(((c+a)*a)*((c*a)*(b+d)))))+(a*((((d*d)*(a*a))*((d*d)-d))*a)))*(d*(c*((d*(a*a))*(c*((b*b)-a))))))))*((d*(b*((a*(c*a))*(((((c*d)*(a*b))*((c*a)*(d-c)))*d)*((((a*b)*d)+b)*d)))))-a));
	let temp_1_2 = (((((c*a)*d)*c)+((b*(b*(c-(((d*(c*a))*d)*b))))*((((((a*a)-(b*a))*((a*a)*(b+d)))*((((b+c)*a)*((a*a)*(b-d)))*(a*(((c+a)*a)*((c*a)*(b+d))))))+(a*((((d*d)*(a*a))*((d*d)-d))*a)))*(d*(c*((d*(a*a))*(c*((b*b)-a))))))))*((d*(b*((a*(c*a))*(((((c*d)*(a*b))*((c*a)*(d-c)))*d)*((((a*b)*d)+b)*d)))))-a));
	calc !{
		(==)
		temp_1_0;
					{lemma_mul_is_associative((((a*a)-(b*a))*((a*a)*(b+d))), (((b+c)*a)*((a*a)*(b-d))), (a*(((c+a)*a)*((c*a)*(b+d)))));
			lemma_mul_is_commutative(c, ((c*a)*d));}// 2
		temp_1_2;
	}
	let temp_2_0 = ((((((a*(c*((c*(a-b))*(a*(d*a)))))*d)-((((a*d)+(a*a))*(((d*(a*b))*((b*d)*d))*d))*(a*d)))*((a*(c*(((c*(c*c))*((d*d)*(d*d)))*c)))*(b*c)))*((((a-((((a*d)*(b*c))*((b*a)*(c*a)))-(((c-d)*(a+b))*((c*d)+(d+a)))))*(a*(((b*(b*c))*b)*(d*d))))*((c*((b*c)*(((a*d)*(b*(31 as int)))*(((4 as int)*(4 as int))*(d*b)))))-(a*a)))*(a*(((a*((b*d)*(c*a)))+((((c*a)*(b+a))*(b*(d+c)))*(d*((a*c)-(c*d)))))*((b*((a+(d*b))*((c*d)*(d*b))))*((d*d)+((c*(b*c))+((a*c)*(d*b)))))))))*((d*((a*(((((d*b)-(c*c))*((b*d)*(b+c)))*(d*c))*(c*(b*((a*c)*(d*d))))))-(((60 as int)-(b+d))*(((((c-b)*(b*d))*((a*d)*b))+d)-((d*((b*d)*(b*b)))-b)))))*(c*((b*a)*((((((c*a)*(d*(36 as int)))*((a-a)+d))*(((b*a)*(b*d))-((b*d)*c)))*a)-((d*(((a*c)*(d*a))+((b*d)*(c*a))))*a))))));
	let temp_2_2 = ((((((a*(c*((c*(a-b))*(a*(d*a)))))*d)-((((a*d)+(a*a))*(((d*(a*b))*((b*d)*d))*d))*(a*d)))*((a*(c*(((c*(c*c))*((d*d)*(d*d)))*c)))*(b*c)))*((((a-((((a*d)*(b*c))*((b*a)*(c*a)))-(((c-d)*(a+b))*((c*d)+(d+a)))))*(a*(((b*(b*c))*b)*(d*d))))*((c*((b*c)*(((a*d)*(b*(31 as int)))*(((4 as int)*(4 as int))*(d*b)))))-(a*a)))*(a*(((a*((b*d)*(c*a)))+((((c*a)*(b+a))*(b*(d+c)))*(d*((a*c)-(c*d)))))*((b*((a+(d*b))*((c*d)*(d*b))))*((d*d)+((c*(b*c))+((a*c)*(d*b)))))))))*((d*((a*(((((d*b)-(c*c))*((b*d)*(b+c)))*(d*c))*(c*(b*((a*c)*(d*d))))))-(((60 as int)-(b+d))*(((((c-b)*(b*d))*((a*d)*b))+d)-((d*((b*d)*(b*b)))-b)))))*(c*((b*a)*((((((c*a)*(d*(36 as int)))*((a-a)+d))*(((b*a)*(b*d))-((b*d)*c)))*a)-((d*(((a*c)*(d*a))+((b*d)*(c*a))))*a))))));
	calc !{
		(==)
		temp_2_0;
					{lemma_mul_is_distributive(((60 as int)-(b+d)), ((((c-b)*(b*d))*((a*d)*b))+d), ((d*((b*d)*(b*b)))-b));
			lemma_mul_is_distributive(((60 as int)-(b+d)), ((((c-b)*(b*d))*((a*d)*b))+d), ((d*((b*d)*(b*b)))-b));}// 2
		temp_2_2;
	}
	let temp_3_0 = (b*(((((((d*((c*c)*(a*a)))*(((a*a)*(a*b))+((b*c)*c)))-(a-(d*((a*d)*d))))*b)*(c*((((c*(d*c))+((a*c)*(b+c)))*(((a*c)*(b*a))*b))*a)))*(((d*d)*(((((d*a)*(a*b))*((c*d)+(c*b)))*(((d*d)*(a*c))*(d-(b*a))))*a))*d))*((c*((d*c)*b))*(b*((a-((a*((a*d)*(d*d)))*c))*(d*(a*a)))))));
	let temp_3_2 = (b*(((((((d*((c*c)*(a*a)))*(((a*a)*(a*b))+((b*c)*c)))-(a-(d*((a*d)*d))))*b)*(c*(((c*(d*c))+((a*c)*(b+c)))*((((a*c)*(b*a))*b)*a))))*(((d*d)*(((((d*a)*(a*b))*(c*(d+b)))*(((d*d)*(a*c))*(d-(b*a))))*a))*d))*((c*((d*c)*b))*(b*((a-((a*((a*d)*(d*d)))*c))*(d*(a*a)))))));
	calc !{
		(==)
		temp_3_0;
					{lemma_mul_is_associative(((c*(d*c))+((a*c)*(b+c))), (((a*c)*(b*a))*b), a);
			lemma_mul_is_distributive(c, d, b);}// 2
		temp_3_2;
	}
	let temp_4_0 = (c*((((a*d)*d)*((((((a*(64 as int))*((c*a)*c))*(b*a))*(c*(b*c)))*(((c*((b+d)*(a*a)))*(((b*d)*(b*b))-c))*c))*((a*(((b*(c*d))*b)*((b*(d*c))*((c*a)*b))))-(b*((((c*a)*(c*c))-(d+(d*c)))*(((d+b)*(a+c))*((c*c)-(d*d))))))))*b));
	let temp_4_2 = (c*((((a*d)*d)*((((((a*(64 as int))*((c*a)*c))*(b*a))*(c*(b*c)))*(((c*((b+d)*(a*a)))*((b*(d*(b*b)))-c))*c))*((a*(((b*(c*d))*b)*((b*(d*c))*((c*a)*b))))-(b*((((c*a)*(c*c))-(d+(d*c)))*((((d+b)*(a+c))*(c*c))-(((d+b)*(a+c))*(d*d))))))))*b));
	calc !{
		(==)
		temp_4_0;
					{lemma_mul_is_distributive(((d+b)*(a+c)), (c*c), (d*d));
			lemma_mul_is_associative(b, d, (b*b));}// 2
		temp_4_2;
	}
	let temp_5_0 = (((c*((d*b)*((b*a)-(d*(((d*(d*b))*((c*a)*(a-d)))-((((41 as int)+d)*c)*((a*d)*(d*d))))))))*a)+((((((c*d)*d)*((((b*a)-(c*(d*a)))-c)*((((b*a)*c)*((d*c)*(b*d)))*(((b*b)*a)*(96 as int)))))*c)+(d+((d*((a*((d*d)+(d*c)))*(((a*d)+(a*a))*((d*d)*a))))*(c*c))))-(((((d-(c*b))*(((c*(a*d))*((c-d)*c))*(c*b)))*(((((b+d)*(b*a))*((d*d)*(d*(69 as int))))*(((c+d)*(b*c))*c))*(((c+(b+d))+((a-b)*(b+a)))*((a*(a*c))*c))))*(d*b))*a)));
	let temp_5_2 = (((c*((d*b)*((b*a)-(d*(((d*(d*b))*((c*a)*(a-d)))-((((41 as int)+d)*c)*((a*d)*(d*d))))))))*a)+((((((c*d)*d)*((((b*a)-(c*(d*a)))-c)*((((b*a)*c)*((d*c)*(b*d)))*(((b*b)*a)*(96 as int)))))*c)+(d+((d*((a*(d*(d+c)))*(((a*d)+(a*a))*((d*d)*a))))*(c*c))))-(((((d-(c*b))*(((c*(a*d))*((c*c)-(d*c)))*(c*b)))*(((((b+d)*(b*a))*((d*d)*(d*(69 as int))))*(((c+d)*(b*c))*c))*(((c+(b+d))+((a-b)*(b+a)))*((a*(a*c))*c))))*(d*b))*a)));
	calc !{
		(==)
		temp_5_0;
					{lemma_mul_is_distributive(c, d, c);
			lemma_mul_is_distributive(d, d, c);}// 2
		temp_5_2;
	}
	let temp_6_0 = (((b*(((d*((((d*a)+(d+d))-(d-(a*d)))*(((b*d)*(c+a))*(b-(d*a)))))+(d-((((d*c)*d)+((b+a)*(d*c)))*(((a*c)+d)*((b*b)+(b*b))))))*(((d*(((c*a)-a)*((b*b)*(c*d))))*b)*((((c*(b*a))*((c*b)*(c*d)))*((d*(a*c))*((a-d)*d)))-a))))+(((7 as int)+((((b*((c*c)*(d*d)))-(d*((c*c)*(d*c))))*c)*(((((b*b)*((3 as int)*d))*(b+(d*b)))+(b*d))*((d*((d-d)*c))-(((b*a)+d)*(d*(36 as int)))))))*c))*((((((((c*(b*c))*((a*d)*d))*a)+((((a*c)*(d*c))*((c*a)-a))*((a*(b+a))*((d*c)*d))))*((d+a)*b))*((a*((a*d)-(((a*d)*(b-d))*((d-c)*(c*b)))))*(b*(((d*a)+c)*(b*((c+c)*(b*b)))))))*(((((a*((a*a)*d))*b)*a)*((a*(((a+b)*a)*((b*d)-(d*b))))*((c*((a*b)*(a*c)))*(((b*d)+(d*b))*d))))*(a*((d*(((b*a)*(b*b))*((b*a)*c)))-((((c*a)*(d*c))*((d*d)*c))*(((a*d)*(c*c))*((d*c)*(b*d))))))))*((c+((c*a)*a))*((24 as int)*((d*((((a-a)*c)*((d*b)*a))*((c*(a*b))*((a*d)*(d*c)))))-b)))));
	let temp_6_2 = (((b*(((d*((((d*a)+(d+d))-(d-(a*d)))*(((b*d)*(c+a))*(b-(d*a)))))+(d-((((d*c)*d)+((b+a)*(d*c)))*(((a*c)+d)*(b*(b+b))))))*(((d*(((c*a)-a)*((b*b)*(c*d))))*b)*((((c*(b*a))*((c*b)*(c*d)))*((d*(a*c))*((a-d)*d)))-a))))+(((7 as int)+((((b*((c*c)*(d*d)))-(d*((c*c)*(d*c))))*c)*(((((b*b)*((3 as int)*d))*(b+(d*b)))+(b*d))*((((d-d)*c)*d)-(((b*a)+d)*(d*(36 as int)))))))*c))*((((((((c*(b*c))*((a*d)*d))*a)+((((a*c)*(d*c))*((c*a)-a))*((a*(b+a))*((d*c)*d))))*((d+a)*b))*((a*((a*d)-(((a*d)*(b-d))*((d-c)*(c*b)))))*(b*(((d*a)+c)*(b*((c+c)*(b*b)))))))*(((((a*((a*a)*d))*b)*a)*((a*(((a+b)*a)*((b*d)-(d*b))))*((c*((a*b)*(a*c)))*(((b*d)+(d*b))*d))))*(a*((d*(((b*a)*(b*b))*((b*a)*c)))-((((c*a)*(d*c))*((d*d)*c))*(((a*d)*(c*c))*((d*c)*(b*d))))))))*((c+((c*a)*a))*((24 as int)*((d*((((a-a)*c)*((d*b)*a))*((c*(a*b))*((a*d)*(d*c)))))-b)))));
	calc !{
		(==)
		temp_6_0;
					{lemma_mul_is_distributive(b, b, b);
			lemma_mul_is_commutative(d, ((d-d)*c));}// 2
		temp_6_2;
	}
	let temp_7_0 = (d*(((((((((a*a)*(a*d))*(0 as int))*(c+(a+c)))-((c*b)+a))*(a+((a-((b*a)+(b*(25 as int))))*(((a*d)*a)*((c*b)*(c*b))))))*(c*(((c*(c*d))*(d*((b+a)*(51 as int))))*c)))+(53 as int))-(b-(d*b))));
	let temp_7_2 = (d*((((c*((((c*c)*d)*(d*((b+a)*(51 as int))))*c))*((((((a*a)*(a*d))*(0 as int))*(c+(a+c)))-((c*b)+a))*(a+((a-((b*a)+(b*(25 as int))))*(((a*d)*a)*((c*b)*(c*b)))))))+(53 as int))-(b-(d*b))));
	calc !{
		(==)
		temp_7_0;
					{lemma_mul_is_commutative(((((((a*a)*(a*d))*(0 as int))*(c+(a+c)))-((c*b)+a))*(a+((a-((b*a)+(b*(25 as int))))*(((a*d)*a)*((c*b)*(c*b)))))), (c*((((c*c)*d)*(d*((b+a)*(51 as int))))*c)));
			lemma_mul_is_associative(c, c, d);}// 2
		temp_7_2;
	}
	let temp_8_0 = (((((((d-(c*((a+c)+(c+d))))*(c*((a*(d*b))-d)))-d)*(((d-((a*(b*d))*a))*c)*((b*((d*(b+d))-b))*d)))*(((((((a*c)*(d*d))+(a*(d*c)))*(b*(d*a)))*(((c*c)*c)*((c*(a-a))*c)))+(((((a*b)*(b*a))*((c-d)*b))*c)-(((b*(a*d))-(d*a))*c)))+((c*a)*d)))*((((((b*c)*(((b*b)*(c*c))*((a+d)+(c+b))))*b)*(((((5 as int)*b)-((b*b)*c))*b)*((c-((c*c)+(b*b)))*(((b*c)*b)*((c*b)*(b*a))))))*((c+(b*(a*(d*(a*b)))))+(((((d*d)*(a*a))*d)-c)*((a*(37 as int))*d))))*(((c*c)*(((((d*c)-(a*a))*((a*a)*(a*d)))*(((d*a)*(a*a))*((b*c)*d)))*((((d*a)*b)*((b*d)*(c*d)))*(((a*b)*b)+d))))*((((((b*d)*(b*(41 as int)))*(c*(a*b)))*(c*((b*d)*c)))-(c*(d*((c-d)*a))))*d))))*((b*((a*c)*((((((b*d)*(b-d))-(c*(c-c)))*(((d*b)*(c*d))*((d*d)*(a*c))))-a)*(d*((c*a)*((c*(d*c))*d))))))*(c-((((c*c)-((((d*d)*(a*a))*((c*b)+c))*a))+b)-(a*((26 as int)*((((b*a)*c)*c)*(a*((c*a)*(b*a))))))))));
	let temp_8_2 = (((((((d-(c*((a+c)+(c+d))))*(c*((a*(d*b))-d)))-d)*(((d-((a*(b*d))*a))*c)*((b*((d*(b+d))-b))*d)))*(((((((a*c)*(d*d))+(a*(d*c)))*(b*(d*a)))*(((c*c)*c)*((c*(a-a))*c)))+(((((a*b)*(b*a))*((c-d)*b))-((b*(a*d))-(d*a)))*c))+((c*a)*d)))*((((((b*c)*(((b*b)*(c*c))*((a+d)+(c+b))))*b)*(((((5 as int)*b)-((b*b)*c))*b)*((c-((c*c)+(b*b)))*(((b*c)*b)*((c*b)*(b*a))))))*((c+(b*(a*(d*(a*b)))))+(((((d*d)*(a*a))*d)-c)*((a*(37 as int))*d))))*(((c*c)*(((((d*c)-(a*a))*((a*a)*(a*d)))*(((d*a)*(a*a))*((b*c)*d)))*((((d*a)*b)*((b*d)*(c*d)))*(((a*b)*b)+d))))*((((((b*d)*(b*(41 as int)))*(c*(a*b)))*(c*((b*d)*c)))-(c*(d*((c-d)*a))))*d))))*((b*((a*c)*((((((b*d)*(b-d))-(c*(c-c)))*(((d*b)*(c*d))*((d*d)*(a*c))))-a)*(d*((c*a)*((c*(d*c))*d))))))*(c-((((c*c)-((((d*d)*(a*a))*((c*b)+c))*a))+b)-(a*((26 as int)*((((b*a)*c)*c)*(a*((b*a)*(c*a))))))))));
	calc !{
		(==)
		temp_8_0;
					{lemma_mul_is_commutative((c*a), (b*a));
			lemma_mul_is_distributive((((a*b)*(b*a))*((c-d)*b)), ((b*(a*d))-(d*a)), c);}// 2
		temp_8_2;
	}
	let temp_9_0 = ((((c*(a*(((d*((d+d)*(c-c)))*d)*((((38 as int)+b)*((a+d)*a))*((a*(b*b))*(d+(a+a)))))))*b)-a)*(((((a*b)*(d*(((b*(b+d))*((4 as int)*(b*a)))*a)))*a)*(((((a-(d*(d*a)))+(c*(d*(d*d))))*c)*a)*((((d*c)*(((d*b)*(b*c))*(a*(a*b))))*((((b*b)-(d*b))+b)-(((c*c)*(c*b))*d)))*(b+((((c*c)*d)-((b*c)*(c*a)))-a)))))*b));
	let temp_9_2 = ((((c*(a*(((d*((d+d)*(c-c)))*d)*((((38 as int)+b)*((a+d)*a))*(((a*(b*b))*d)+((a*(b*b))*(a+a)))))))*b)-a)*(((((a*b)*(d*(((b*(b+d))*((4 as int)*(b*a)))*a)))*a)*(((((a-(d*(d*a)))+(c*(d*(d*d))))*c)*a)*((((d*c)*(((d*b)*(b*c))*(a*(a*b))))*((((b*b)-(d*b))+b)-(((c*c)*(c*b))*d)))*(b+(((d*(c*c))-((b*c)*(c*a)))-a)))))*b));
	calc !{
		(==)
		temp_9_0;
					{lemma_mul_is_commutative((c*c), d);
			lemma_mul_is_distributive((a*(b*b)), d, (a+a));}// 2
		temp_9_2;
	}
	let temp_10_0 = (((((c*(((b-b)*(((a+d)*b)*a))*b))+((a*((c*((d+c)*b))*(((c+b)*(d+b))*((c*d)*c))))*(b*(((b-(b*d))*a)+(((d*a)*(b*a))*((c-c)-b))))))*(((a*((c*(a*(c*b)))*(((c*a)+(a*a))*((d*d)*(d*a)))))*((c*((d*b)*((c*d)-c)))*((((b*a)*((85 as int)+d))*((a*(43 as int))*(a-a)))*b)))+((((((a*b)*(a*d))*(d*b))*((a*(c*a))*(c+(a*d))))*((((d*d)+(d-c))*((a*a)+(c*b)))*c))*b)))*((3 as int)*d))*(((b*(a*(((((c*(52 as int))*(a*(42 as int)))*(c*b))*(((d*d)-(d*a))*(b-((6 as int)*d))))-(((b-b)-d)+(a*c)))))*(((((((b+c)*(d*a))*((b*b)+(b*c)))+((d*d)*((d*d)*c)))*(d-(((b*c)*(b*a))*a)))*(((((d*a)*(a*d))*((c+d)*(d*d)))*(a+((a*d)*a)))*(((21 as int)*((d+c)+(a*a)))*(((a*a)*(c*a))*((d*d)*(b-a))))))*b))*(((c+(((((b*c)+(d-b))*(d*(c*c)))+((c*(d-b))*((d*b)*(c*d))))*(d*(((d*d)*(d*c))*((b*(12 as int))*b)))))*(b*(a*(((a*b)*c)*(((a*b)*b)*(c*(a*d)))))))+((c*(d*d))*d))));
	let temp_10_2 = (((((c*(((b-b)*(((a+d)*b)*a))*b))+((a*((c*((d+c)*b))*(((c+b)*(d+b))*((c*d)*c))))*(b*(((b-(b*d))*a)+(((d*a)*(b*a))*((c-c)-b))))))*(((a*((c*(a*(c*b)))*(((c*a)+(a*a))*((d*d)*(d*a)))))*((c*((d*b)*((c*d)-c)))*((((b*a)*((85 as int)+d))*((a*(43 as int))*(a-a)))*b)))+((((((a*b)*(a*d))*(d*b))*((a*(c*a))*(c+(a*d))))*((((d*d)+(d-c))*((a*a)+(c*b)))*c))*b)))*((3 as int)*d))*(((b*(a*(((((c*(52 as int))*(a*(42 as int)))*(c*b))*(((d*d)-(d*a))*(b-((6 as int)*d))))-(((b-b)-d)+(a*c)))))*(((((((b+c)*(d*a))*((b*b)+(b*c)))+((d*d)*((d*d)*c)))*(d-(((b*c)*(b*a))*a)))*(((((d*a)*(a*d))*((c+d)*(d*d)))*(a+((a*d)*a)))*(((21 as int)*((d+c)+(a*a)))*(((a*a)*(c*a))*((d*d)*(b-a))))))*b))*(((c+(((((b*c)+(d-b))*(d*(c*c)))+((c*(d-b))*((d*b)*(c*d))))*(d*(((d*d)*(d*c))*((b*(12 as int))*b)))))*(b*(a*(((a*b)*c)*(((a*b)*b)*(c*(a*d)))))))+((c*(d*d))*d))));
	calc !{
		(==)
		temp_10_0;
					{lemma_mul_is_distributive(a, d, b);
			lemma_mul_is_distributive(a, d, b);}// 2
		temp_10_2;
	}
	let temp_11_0 = ((((((b*a)*b)+((b*c)*(((((c*c)*(d*b))*d)*d)*((((b*b)*(d*d))*a)*((c*(c*d))*(b-(a*c)))))))*(c*c))*(((8 as int)-((((((c*a)-(c*d))*d)*(b*a))*((((b*d)+d)*(d*a))*(((c-a)*(c*a))*d)))*(c-d)))*(b+((((((b*a)*(a*a))*((d*b)*(c*d)))*(((d*c)*(d*d))*((c*d)*(c*c))))*(71 as int))*(d*c)))))*b);
	let temp_11_2 = ((((((b*a)*b)+((b*c)*(((((c*c)*(d*b))*d)*d)*((((b*b)*(d*d))*a)*((c*(c*d))*(b-(a*c)))))))*(c*c))*(((8 as int)-((((c*(a-d))*d)*(b*a))*(((((b*d)+d)*(d*a))*(((c-a)*(c*a))*d))*(c-d))))*(b+((((((b*a)*(a*a))*((d*b)*(c*d)))*(((d*c)*(d*d))*((c*d)*(c*c))))*(71 as int))*(d*c)))))*b);
	calc !{
		(==)
		temp_11_0;
					{lemma_mul_is_associative((((c*(a-d))*d)*(b*a)), ((((b*d)+d)*(d*a))*(((c-a)*(c*a))*d)), (c-d));
			lemma_mul_is_distributive(c, a, d);}// 2
		temp_11_2;
	}
	let temp_12_0 = (((((a*b)*(((d*d)-((b-(b+(c*a)))-c))+(a*((a*((a*a)-(a*c)))+(59 as int)))))+(b*b))*(b*(a*a)))-(c+((((((((c+a)*(b*c))*((d*d)-(a*c)))*(((b*a)-(d*c))*d))-(c+d))-(b-a))*(c*(((((d*c)+c)+((b*d)*a))*d)*((c*((b-c)*(b*d)))+(((b*a)*b)*c)))))*a)));
	let temp_12_2 = (((((a*b)*(((d*d)-((b-(b+(c*a)))-c))+(a*((a*((a*a)-(a*c)))+(59 as int)))))+(b*b))*(b*(a*a)))-(c+((((((((c+a)*(b*c))*((d*d)-(a*c)))*(((b*a)-(d*c))*d))-(c+d))-(b-a))*((c*((((d*c)+c)+((b*d)*a))*d))*((c*((b-c)*(b*d)))+(((b*a)*b)*c))))*a)));
	calc !{
		(==)
		temp_12_0;
					{lemma_mul_is_associative(c, ((((d*c)+c)+((b*d)*a))*d), ((c*((b-c)*(b*d)))+(((b*a)*b)*c)));
			lemma_mul_is_commutative(b, b);}// 2
		temp_12_2;
	}
	let temp_13_0 = (((c-(b-(a*(c*((((b*b)*(a*c))*(b*(b*a)))*(((a*b)-d)*(b*(b*d))))))))*((b*((b*(b+((b*(d*d))*(a*(b+b)))))*a))*c))*((a*(((d*(c*a))*(((38 as int)*c)*(c+((a*(b*c))*a))))*((((((a*c)*(79 as int))*(b*(d-a)))*(c*c))*a)*a)))*((b-((((((c*b)*(a*c))*((c*b)*(a*a)))*b)*(a*(((d*d)*((18 as int)*d))-((b*b)-(c*a)))))*(((c*((c*c)*(c*b)))*((c*(a*b))*((b*b)*(b*d))))*((((b*d)*(a+a))*a)*(((c-a)*(a*c))*((d-c)+(d*a)))))))*(((c*(((b*(b-d))-((b*a)-(b*a)))+(((c*a)*(80 as int))*((d+c)*(d*c)))))*(d*(c*(((d*d)*(a*d))*((b+a)*a)))))*c))));
	let temp_13_2 = (((c-(b-(a*((c*(((b*b)*(a*c))*(b*(b*a))))*(((a*b)-d)*(b*(b*d)))))))*((b*((b*(b+((b*(d*d))*(a*(b+b)))))*a))*c))*((a*(((d*(c*a))*(((38 as int)*c)*(c+((a*(b*c))*a))))*((((((a*c)*(79 as int))*(b*(d-a)))*(c*c))*a)*a)))*((b-((((((c*b)*(a*c))*((c*b)*(a*a)))*b)*(a*(((d*d)*((18 as int)*d))-((b*b)-(c*a)))))*(((c*((c*c)*(c*b)))*((c*(a*b))*((b*b)*(b*d))))*((((b*d)*(a+a))*a)*(((c-a)*(a*c))*((d-c)+(d*a)))))))*(((c*(((b*(b-d))-(b*(a-a)))+(((c*a)*(80 as int))*((d+c)*(d*c)))))*(d*(c*(((d*d)*(a*d))*((b+a)*a)))))*c))));
	calc !{
		(==)
		temp_13_0;
					{lemma_mul_is_associative(c, (((b*b)*(a*c))*(b*(b*a))), (((a*b)-d)*(b*(b*d))));
			lemma_mul_is_distributive(b, a, a);}// 2
		temp_13_2;
	}
	let temp_14_0 = ((((((((((d*a)*(a*b))-c)*d)*((((b*(61 as int))*(d*d))*((a+d)-(a*c)))*(b*(c*(c+b)))))*a)+((((((a*(91 as int))*(d*d))*(b*c))*c)*(c*(a*((a+a)*(a*a)))))*d))*(((((((d+a)+(a*c))*((d*a)-c))+(((c*a)*(d*b))*d))+c)*d)*(((((b*(d*a))+((d*a)*(b*a)))*(a*((d*b)*(c*d))))*((((a*b)*(d*d))*(d*(a*b)))*(((c*d)*c)-(a*a))))*((((a*(c*a))*(c*(b*d)))+a)-((c*b)*(((c*b)*(d*a))*((b+d)*(b*d))))))))+(((((((d*(c*a))*(b+(b*d)))*c)*((((b-b)*(b*c))*((a*c)*(d-a)))*((c*(c*c))*(d*(b*d)))))*c)*d)*(((((b*((c*c)*(c*b)))*a)*((((d*b)*d)*((b-b)*(c*d)))*a))*b)*a)))+((c*(((a-b)-(((((d-c)*(b*c))*c)*(((b*d)*b)*c))*a))*((c*((((c*a)*c)*(a-d))*(((a*b)-(c*b))*((c*d)*(c*c)))))*(((((d*c)*(a*d))*((a*d)-(b*b)))*c)-((((a*c)*(b*d))+((d*d)+d))+(c*(b-(d*c))))))))*c));
	let temp_14_2 = ((((((((((d*a)*(a*b))-c)*d)*((((b*(61 as int))*(d*d))*((a+d)-(a*c)))*(b*(c*(c+b)))))*a)+((((((a*(91 as int))*(d*d))*(b*c))*c)*(c*(a*((a+a)*(a*a)))))*d))*(((((((d+a)+(a*c))*((d*a)-c))+(((c*a)*(d*b))*d))+c)*d)*(((((b*(d*a))+((d*a)*(b*a)))*(a*((d*b)*(c*d))))*((((a*b)*(d*d))*((d*a)*b))*(((c*d)*c)-(a*a))))*((((a*(c*a))*(c*(b*d)))+a)-((c*b)*(((c*b)*(d*a))*((b+d)*(b*d))))))))+(((((((d*(c*a))*(b+(b*d)))*c)*((((b-b)*(b*c))*(((a*c)*d)-((a*c)*a)))*((c*(c*c))*(d*(b*d)))))*c)*d)*(((((b*((c*c)*(c*b)))*a)*((((d*b)*d)*((b-b)*(c*d)))*a))*b)*a)))+((c*(((a-b)-(((((d-c)*(b*c))*c)*(((b*d)*b)*c))*a))*((c*((((c*a)*c)*(a-d))*(((a*b)-(c*b))*((c*d)*(c*c)))))*(((((d*c)*(a*d))*((a*d)-(b*b)))*c)-((((a*c)*(b*d))+((d*d)+d))+(c*(b-(d*c))))))))*c));
	calc !{
		(==)
		temp_14_0;
					{lemma_mul_is_associative(d, a, b);
			lemma_mul_is_distributive((a*c), d, a);}// 2
		temp_14_2;
	}
	let temp_15_0 = ((((c*(d*(((d*((a*b)*(d*d)))*(a*((c+c)*b)))*d)))*((b*(((c+((b*c)-a))*a)*((((c*b)*(b*b))*d)*(((a*c)*(b*d))*(b*c)))))*((((a*((c*b)*(b*c)))*a)*b)*a)))*((((((((a*c)*(c*d))*((a*b)*(b*c)))*a)*a)*c)*(((b*(((b*c)*(c*a))*((c*a)*a)))*b)-b))*(16 as int)))*(9 as int));
	let temp_15_2 = ((((c*(d*(((d*((a*b)*(d*d)))*(a*((c+c)*b)))*d)))*((b*(((c*a)+(((b*c)-a)*a))*((((c*b)*(b*b))*d)*(((a*c)*(b*d))*(b*c)))))*((((a*((c*b)*(b*c)))*a)*b)*a)))*(((((b*(((b*c)*(c*a))*((c*a)*a)))*b)-b)*((((((a*c)*(c*d))*((a*b)*(b*c)))*a)*a)*c))*(16 as int)))*(9 as int));
	calc !{
		(==)
		temp_15_0;
					{lemma_mul_is_distributive(c, ((b*c)-a), a);
			lemma_mul_is_commutative(((((((a*c)*(c*d))*((a*b)*(b*c)))*a)*a)*c), (((b*(((b*c)*(c*a))*((c*a)*a)))*b)-b));}// 2
		temp_15_2;
	}
	let temp_16_0 = ((b*(((((b*(((a*b)*a)*d))+(d*d))*(((((d*b)*a)+b)*c)*((((d*b)*(c*a))*(b-(d*d)))*a)))*(d+((((a*(c*a))*a)*(d*b))-((((d*d)*d)*((d*c)*b))*(((a*b)*d)*((c*c)*(b-a)))))))*b))*(((c*((((((d*b)*(a*c))*((a*c)*(d-d)))*b)+((d+b)+((a*(c*c))*d)))*((d*d)*((((b*b)*d)*b)*b))))*(((b*((b*((b*a)*(b*c)))*d))*((40 as int)+((d*c)*(b*a))))*(d*(c*(((46 as int)*((b*d)*(b*c)))*(a*((c*d)*c)))))))-a));
	let temp_16_2 = ((b*(((((b*(((a*b)*a)*d))+(d*d))*(((((d*b)*a)+b)*c)*((((d*b)*(c*a))*(b-(d*d)))*a)))*(d+((((a*(c*a))*a)*(d*b))-((((d*d)*d)*((d*c)*b))*(((a*b)*d)*((c*c)*(b-a)))))))*b))*(((c*((((((d*b)*(a*c))*(((a*c)-(a*c))*d))*b)+((d+b)+((a*(c*c))*d)))*((d*d)*((((b*b)*d)*b)*b))))*(((b*((b*((b*a)*(b*c)))*d))*((40 as int)+((d*c)*(b*a))))*(d*(c*(((46 as int)*((b*d)*(b*c)))*(a*((c*d)*c)))))))-a));
	calc !{
		(==)
		temp_16_0;
					{lemma_mul_is_distributive((a*c), (a*c), d);
			lemma_mul_is_distributive((a*c), d, d);}// 2
		temp_16_2;
	}
	let temp_17_0 = ((((((d*((((b*d)*d)*d)*((a*(a+d))*((b*c)*(d*d)))))-b)*((((((b*d)*(d*b))*((a*c)-(d*a)))*a)+(((a*c)*(a*a))*(c*((b*b)*c))))*(((d*((c*d)+(c-b)))*c)*a)))*(((((a+((c*c)*(a*(5 as int))))*(((c*d)*(c*b))*(a*(d*d))))-((a*(c*(b+b)))*(((b*a)*(b*b))*((a-d)*(d*a)))))*b)-(52 as int)))*d)+((c*(((((d*d)*(c*((d*a)*a)))*(b*b))*(((b*d)*((b*b)*((b*b)*b)))*a))*(a*(c-((d*b)*((d*b)*d))))))*(((d+(((((a*b)*(d-b))*((b*a)+(a-d)))*a)*(c*a)))*(c*((((b*(a*d))-((c*a)-(a*c)))*(((d*c)*(d*c))-((d*c)*(c-a))))+a)))-((((d-(((a*a)*(a*d))+(c+(a-a))))+b)+((d*b)+b))*((((d+((b-a)*c))*d)*(b*(((a-d)*(a*c))*(c+c))))*(b*(b*(b*((c*b)*(b-c))))))))));
	let temp_17_2 = ((((((d*((((b*d)*d)*d)*((a*(a+d))*((b*c)*(d*d)))))-b)*((((((b*d)*(d*b))*((a*c)-(d*a)))*a)+(((a*c)*(a*a))*(c*((b*b)*c))))*(((d*((c*d)+(c-b)))*c)*a)))*(((((a+((c*c)*(a*(5 as int))))*(((c*d)*(c*b))*(a*(d*d))))-((a*(c*(b+b)))*(((b*a)*(b*b))*((a-d)*(d*a)))))*b)-(52 as int)))*d)+((c*(((((d*d)*(c*((d*a)*a)))*(b*b))*(((b*d)*((b*b)*((b*b)*b)))*a))*(a*(c-((d*b)*((d*b)*d))))))*(((d+((a*(((a*b)*(d-b))*((b*a)+(a-d))))*(c*a)))*(c*((((b*(a*d))-((c*a)-(a*c)))*(((d*c)*(d*c))-(d*(c*(c-a)))))+a)))-((((d-(((a*a)*(a*d))+(c+(a-a))))+b)+((d*b)+b))*((((d+((b-a)*c))*d)*(b*(((a-d)*(a*c))*(c+c))))*(b*(b*(b*((c*b)*(b-c))))))))));
	calc !{
		(==)
		temp_17_0;
					{lemma_mul_is_commutative((((a*b)*(d-b))*((b*a)+(a-d))), a);
			lemma_mul_is_associative(d, c, (c-a));}// 2
		temp_17_2;
	}
	let temp_18_0 = (((c*d)*b)+((((((((b+(c*a))*((d*(7 as int))-(d*c)))*(a-b))*(c*((b*(d*d))*((c*d)*(c*a)))))*b)*(94 as int))*(((((((d*c)+(b+a))*((d*c)*(c*d)))*((c*(c*b))*((a*b)*(83 as int))))*(((c*b)*c)+(((b*b)*(b*d))*a)))*((c-(((d*c)*(a*c))*((b*d)*(c-c))))*(a*(c*(b*(d*a))))))*(((a*(((c*c)+(c*a))*((d-a)*(c*c))))*a)-(b*((((c*c)*c)*(b+(b+d)))-b)))))*b));
	let temp_18_2 = (((c*d)*b)+((((((((b+(c*a))*((d*(7 as int))-(d*c)))*(a-b))*(c*((b*(d*d))*((c*d)*(c*a)))))*b)*(94 as int))*((((((((d*c)+(b+a))*((d*c)*(c*d)))*((c*(c*b))*((a*b)*(83 as int))))*((c*b)*c))+(((((d*c)+(b+a))*((d*c)*(c*d)))*((c*(c*b))*((a*b)*(83 as int))))*(((b*b)*(b*d))*a)))*((c-(((d*c)*(a*c))*((b*d)*(c-c))))*(a*(c*(b*(d*a))))))*(((a*(((c*c)*((d-a)*(c*c)))+((c*a)*((d-a)*(c*c)))))*a)-(b*((((c*c)*c)*(b+(b+d)))-b)))))*b));
	calc !{
		(==)
		temp_18_0;
					{lemma_mul_is_distributive(((((d*c)+(b+a))*((d*c)*(c*d)))*((c*(c*b))*((a*b)*(83 as int)))), ((c*b)*c), (((b*b)*(b*d))*a));
			lemma_mul_is_distributive((c*c), (c*a), ((d-a)*(c*c)));}// 2
		temp_18_2;
	}
	let temp_19_0 = ((((((c+(((b*(a-c))*(a*(c+b)))-c))*b)-(((d*c)*((c*(b*(d*a)))-a))*((((a*b)*d)*(((c*c)*(b*b))*((a*a)*d)))*((((d*c)*(a*b))+(d*d))-(((a*b)+(b-c))*(d*(b-b)))))))*((b*(((((c-c)*(b*b))*((b+b)*a))+(((c*c)*(d*c))*((d*c)*a)))*((b*((b*a)*(a*d)))*(((b+d)*(b*c))*b))))*d))-((((a*(((a*(d-b))*(d*(c*c)))*a))*c)+((((((c*a)*b)*((b*c)*d))*(((a-b)*c)*(((29 as int)+a)*(b+b))))*a)*(((b*((b-a)*(c*a)))*d)*(b*c))))*(c*d)))*((((b-(((((d*d)*(c*d))*c)*a)*d))-a)-(b*(((c*c)*((a+((a*b)*(c*b)))*(a*((d*c)*(c+b)))))*(((b+((c*c)*(c-c)))*((c*a)+c))*(d*d)))))*((b*((((d*((d*b)-c))*((d*(b*b))*(a*(d*b))))*((((b*c)*(c-d))-b)+(b*((d*b)*c))))*(((d*((b*d)*(b*b)))*(((c*c)*b)*d))*((((d*d)*(a*b))*b)-a))))*(((((b*((a-b)-(a*c)))*((b*a)*(c*(a-d))))*((d+((d*a)*(b*b)))*(((a*a)*(d+a))-(b*(d*c)))))*a)*a))));
	let temp_19_2 = ((((((c+(((b*(a-c))*(a*(c+b)))-c))*b)-(((d*c)*((c*((b*d)*a))-a))*((((a*b)*d)*(((c*c)*(b*b))*((a*a)*d)))*((((d*c)*(a*b))+(d*d))-(((a*b)+(b-c))*(d*(b-b)))))))*((b*(((((c-c)*(b*b))*((b+b)*a))+(((c*c)*(d*c))*((d*c)*a)))*((b*((b*a)*(a*d)))*(((b+d)*(b*c))*b))))*d))-((((a*(((a*(d-b))*(d*(c*c)))*a))*c)+((((((c*a)*b)*((b*c)*d))*(((a-b)*c)*(((29 as int)+a)*(b+b))))*a)*(((b*((b-a)*(c*a)))*d)*(b*c))))*(c*d)))*((((b-(((((d*d)*(c*d))*c)*a)*d))-a)-(b*(((c*c)*((a+((a*b)*(c*b)))*(a*((d*c)*(c+b)))))*(((b+((c*c)*(c-c)))*((c*a)+c))*(d*d)))))*((b*((((d*((d*b)-c))*((d*(b*b))*(a*(d*b))))*((((b*c)*(c-d))-b)+(b*((d*b)*c))))*(((d*((b*d)*(b*b)))*(((c*c)*b)*d))*((((d*d)*(a*b))*b)-a))))*(((((b*((a-b)-(a*c)))*((b*a)*((c*a)-(c*d))))*((d+((d*a)*(b*b)))*(((a*a)*(d+a))-(b*(d*c)))))*a)*a))));
	calc !{
		(==)
		temp_19_0;
					{lemma_mul_is_distributive(c, a, d);
			lemma_mul_is_associative(b, d, a);}// 2
		temp_19_2;
	}
	let temp_20_0 = ((((c-d)*(d+((((((b+a)*(d-c))*((a*a)*d))+d)+(d*(((b*a)*(d*a))*((c+a)*(a*d)))))*(((((b*d)+(b*d))*((c*b)*(a*c)))*((d*(b*d))*((b*b)*(b*a))))-d))))*(b*((c*((((c*d)*((d*a)*(a-b)))*(((a*a)+(c*d))+c))*((((a*d)*(c-b))+((c-a)*b))*(d*((d-d)*d)))))*((((((a*b)+(c*(84 as int)))*((a-a)*(a-d)))-b)*((b*((b*d)*(b*c)))*((c-(d*a))*a)))*(((((a*c)*d)*(a*(a-a)))+b)-b)))))*((((c*a)-((((((b+d)*(d-c))*b)*c)*a)*(((((d*c)*c)*((a*b)*(c*d)))*c)+d)))*((((c*(((a*d)*b)*((b-c)*a)))*(((((3 as int)*c)*(c*b))-d)*(((b*c)*(c*a))*((d+a)*(b*d)))))*(d-(((b*(b*a))*((d*b)-a))*(a*(((54 as int)*c)*a)))))*(b*(d*(a*c)))))*(12 as int)));
	let temp_20_2 = ((((c-d)*(d+((((((b+a)*(d-c))*((a*a)*d))+d)+(d*(((b*a)*(d*a))*((c+a)*(a*d)))))*((((b*(d+d))*(((c*b)*a)*c))*((d*(b*d))*((b*b)*(b*a))))-d))))*(b*((c*((((c*d)*((d*a)*(a-b)))*(((a*a)+(c*d))+c))*((((a*d)*(c-b))+((c-a)*b))*(d*((d-d)*d)))))*((((((a*b)+(c*(84 as int)))*((a-a)*(a-d)))-b)*((b*((b*d)*(b*c)))*((c-(d*a))*a)))*(((((a*c)*d)*(a*(a-a)))+b)-b)))))*((((c*a)-((((((b+d)*(d-c))*b)*c)*a)*(((((d*c)*c)*((a*b)*(c*d)))*c)+d)))*((((c*(((a*d)*b)*((b-c)*a)))*(((((3 as int)*c)*(c*b))-d)*(((b*c)*(c*a))*((d+a)*(b*d)))))*(d-(((b*(b*a))*((d*b)-a))*(a*(((54 as int)*c)*a)))))*(b*(d*(a*c)))))*(12 as int)));
	calc !{
		(==)
		temp_20_0;
					{lemma_mul_is_distributive(b, d, d);
			lemma_mul_is_associative((c*b), a, c);}// 2
		temp_20_2;
	}
	let temp_21_0 = ((((b*b)*d)+((((c*(((d*(a*b))*((a*d)*(a*d)))+(((b*c)*(d*a))*((a-c)+a))))*(a*(((c+c)-a)*(b*a))))*(98 as int))*((d+(((((d*b)*(d-b))*d)*(((a-a)*(a*d))*a))*a))*((a+(c*(((d*a)*(a*b))-((b*d)-b))))*(d*a)))))*a);
	let temp_21_2 = ((((b*b)*d)+(((((((d*(a*b))*((a*d)*(a*d)))+(((b*c)*(d*a))*((a-c)+a)))*c)*(a*(((c+c)-a)*(b*a))))*(98 as int))*((d+(((((d*b)*(d-b))*d)*(((a*(a*d))-(a*(a*d)))*a))*a))*((a+(c*(((d*a)*(a*b))-((b*d)-b))))*(d*a)))))*a);
	calc !{
		(==)
		temp_21_0;
					{lemma_mul_is_commutative(c, (((d*(a*b))*((a*d)*(a*d)))+(((b*c)*(d*a))*((a-c)+a))));
			lemma_mul_is_distributive(a, a, (a*d));}// 2
		temp_21_2;
	}
	let temp_22_0 = (c*(a*(c*(((b*(a*a))*(a*(c*((92 as int)*((b*b)*c)))))*((b*((((c-c)-(a*d))*c)*c))*(a*(a*(a*(a*b)))))))));
	let temp_22_2 = (c*(a*(c*(((b*(a*a))*((c*((92 as int)*(c*(b*b))))*a))*((b*((((c-c)-(a*d))*c)*c))*(a*(a*(a*(a*b)))))))));
	calc !{
		(==)
		temp_22_0;
					{lemma_mul_is_commutative((b*b), c);
			lemma_mul_is_commutative(a, (c*((92 as int)*((b*b)*c))));}// 2
		temp_22_2;
	}
	let temp_23_0 = ((c*a)*((((b*(((((d*d)*a)*c)*d)*((d*((a*(79 as int))*(c*a)))*(((b+b)*(a-c))*((d*b)-(c*d))))))-a)*(((((b*c)*((a-(b*a))*(d*(c+a))))*(a*(((d-b)*(b*c))+b)))*(((c*((d*b)+(b*b)))+(((d*b)*(a*c))*c))*((b*b)*((c*(b*a))*(c*(a*a))))))-c))-(((a*(c*(((d*(a*a))*((a*a)*(a*b)))*c)))-((b*((b*c)*(((c*d)*a)*((a*a)+c))))*(((((b*b)*d)+((c*c)+(a+d)))*((c*(a-a))*(17 as int)))*((a*((97 as int)*(b*d)))*(((d*c)*(c*b))*c)))))*d)));
	let temp_23_2 = ((c*a)*((((b*((((a*(d*d))*c)*d)*((d*((a*(79 as int))*(c*a)))*(((b+b)*(a-c))*((d*b)-(c*d))))))-a)*(((((b*c)*((a*(d*(c+a)))-((b*a)*(d*(c+a)))))*(a*(((d-b)*(b*c))+b)))*(((c*((d*b)+(b*b)))+(((d*b)*(a*c))*c))*((b*b)*((c*(b*a))*(c*(a*a))))))-c))-(((a*(c*(((d*(a*a))*((a*a)*(a*b)))*c)))-((b*((b*c)*(((c*d)*a)*((a*a)+c))))*(((((b*b)*d)+((c*c)+(a+d)))*((c*(a-a))*(17 as int)))*((a*((97 as int)*(b*d)))*(((d*c)*(c*b))*c)))))*d)));
	calc !{
		(==)
		temp_23_0;
					{lemma_mul_is_distributive(a, (b*a), (d*(c+a)));
			lemma_mul_is_commutative((d*d), a);}// 2
		temp_23_2;
	}
	let temp_24_0 = (((d*((((d*b)+(((((88 as int)*d)*(a*c))*((b*c)*(b+b)))*(((a*a)+(c*b))*(d-(d*d)))))*a)*((((((d*a)*d)*((b*b)*c))+(b-b))+(a*(a*(d*(d*a)))))*(((b*b)*(((b+a)*(c*c))*((b*d)*(b*b))))*((((d*d)*a)*b)+(((a*d)*(d*b))*((b+b)*(b*c))))))))*c)*(((((a*(a*(((c+d)*(d+c))*a)))*(((d*a)*d)+c))*(b*(((d*((c*a)+((46 as int)-d)))-c)*a)))*((d*b)+a))*((a-(c*b))*c)));
	let temp_24_2 = (((((((d*b)+(((((88 as int)*d)*(a*c))*((b*c)*(b+b)))*(((a*a)+(c*b))*(d-(d*d)))))*a)*((((((d*a)*d)*((b*b)*c))+(b-b))+(a*(a*(d*(d*a)))))*(((b*b)*(((b+a)*(c*c))*((b*d)*(b*b))))*((((d*d)*a)*b)+(((a*d)*(d*b))*((b+b)*(b*c)))))))*d)*c)*(((((a*(a*(((c+d)*(d+c))*a)))*(((d*a)*d)+c))*(b*(((d*((c*a)+((46 as int)-d)))-c)*a)))*((b*d)+a))*((a-(c*b))*c)));
	calc !{
		(==)
		temp_24_0;
					{lemma_mul_is_commutative(d, b);
			lemma_mul_is_commutative(d, ((((d*b)+(((((88 as int)*d)*(a*c))*((b*c)*(b+b)))*(((a*a)+(c*b))*(d-(d*d)))))*a)*((((((d*a)*d)*((b*b)*c))+(b-b))+(a*(a*(d*(d*a)))))*(((b*b)*(((b+a)*(c*c))*((b*d)*(b*b))))*((((d*d)*a)*b)+(((a*d)*(d*b))*((b+b)*(b*c))))))));}// 2
		temp_24_2;
	}
	let temp_25_0 = (((a*(b*((a*((((c*a)+(a*a))*(c*(d*a)))*(((a*b)*(b+c))*((b+b)*(c*c)))))*(d*(((b+(d*d))-a)*(((b*a)*c)*((a*d)*(b*b))))))))*(c*(((((a*a)+d)*b)*(d*(b*(d*((c*a)-(b*d))))))*(b*(94 as int)))))*((a*((((b*((a*b)+(a*(a-c))))*((((b*d)+(a*d))*d)*b))+(((((c*b)*(a*(84 as int)))*d)+((a*d)*((a*(58 as int))*d)))*((((b*a)-c)*((d*d)*(c*c)))*c)))*((((((b+c)*(d*a))*((c*a)*(a*d)))-((b-b)*(c*b)))*((b*c)*(d-d)))*c)))*((d-((((a*((b*a)*(a+a)))*(b*a))*((((c*b)*b)*((c*c)*(d*c)))*c))*(((a-((d-d)*(c*d)))*(c*((a*a)*(a+a))))*((b*a)+(((d*c)*(c*d))*(b-(d+b)))))))*((((c*(c*((a-a)*(a*a))))*((d*d)*((b*(c*a))-c)))*((((d*(d*d))*(a*a))*c)*b))*(c-(((d*((d*c)*c))*(((d*d)-d)*((a*b)*(c*d))))+a))))));
	let temp_25_2 = (((a*(b*((a*((((c*a)*(c*(d*a)))+((a*a)*(c*(d*a))))*(((a*b)*(b+c))*((b*(c*c))+(b*(c*c))))))*(d*(((b+(d*d))-a)*(((b*a)*c)*((a*d)*(b*b))))))))*(c*(((((a*a)+d)*b)*(d*(b*(d*((c*a)-(b*d))))))*(b*(94 as int)))))*((a*((((b*((a*b)+(a*(a-c))))*((((b*d)+(a*d))*d)*b))+(((((c*b)*(a*(84 as int)))*d)+((a*d)*((a*(58 as int))*d)))*((((b*a)-c)*((d*d)*(c*c)))*c)))*((((((b+c)*(d*a))*((c*a)*(a*d)))-((b-b)*(c*b)))*((b*c)*(d-d)))*c)))*((d-((((a*((b*a)*(a+a)))*(b*a))*((((c*b)*b)*((c*c)*(d*c)))*c))*(((a-((d-d)*(c*d)))*(c*((a*a)*(a+a))))*((b*a)+(((d*c)*(c*d))*(b-(d+b)))))))*((((c*(c*((a-a)*(a*a))))*((d*d)*((b*(c*a))-c)))*((((d*(d*d))*(a*a))*c)*b))*(c-(((d*((d*c)*c))*(((d*d)-d)*((a*b)*(c*d))))+a))))));
	calc !{
		(==)
		temp_25_0;
					{lemma_mul_is_distributive((c*a), (a*a), (c*(d*a)));
			lemma_mul_is_distributive(b, b, (c*c));}// 2
		temp_25_2;
	}
	let temp_26_0 = (((((((d*(((a-d)-(c*b))+a))*(b*((b*(b*a))*((c*b)*((35 as int)+c)))))*((((b*(b*a))*((d+c)*(a*d)))-(((b*d)*(b*c))*a))*((((c-c)*(b-a))*(b*(d*c)))+(((b-a)*(a*a))-c))))*(d*((d*((0 as int)*((d*b)-(b*b))))*(((a-d)*c)*a))))*(((((((d*b)-(a*c))+((d*d)*c))*d)*((((c*d)*(d*b))+(((9 as int)*b)*(d*a)))*(((b*a)*d)*(a*(c*d)))))*(b*b))*(c*(((((a-c)+(d+a))*(a*(d+b)))+b)*((((d*b)*b)*(((24 as int)*a)*a))*d)))))*(a+((a*c)*(d+b))))*((((b*((c*a)*d))*b)*(((((b-b)*(((d*c)*(b*c))*((c*b)-(b*d))))*(c*(c*d)))+((d*(((a*d)*(a*c))*c))-(b+(((a*a)+(c*a))*a))))*(((b*((a+(d*d))*(a+(d*d))))+b)*d)))*((b*((c*b)*((d*((d-(a*b))+((c*c)*(c*b))))*c)))*a)));
	let temp_26_2 = (((((((d*(((a-d)-(c*b))+a))*(b*(((b*b)*a)*((c*b)*((35 as int)+c)))))*((((b*(b*a))*((d+c)*(a*d)))-(((b*d)*(b*c))*a))*((((c-c)*(b-a))*(b*(d*c)))+(((b-a)*(a*a))-c))))*(d*((d*((0 as int)*((d*b)-(b*b))))*(((a-d)*c)*a))))*(((((((d*b)-(a*c))+((d*d)*c))*d)*((((c*d)*(d*b))+(((9 as int)*b)*(d*a)))*(((b*a)*d)*(a*(c*d)))))*(b*b))*(c*(((((a-c)+(d+a))*(a*(d+b)))+b)*((((d*b)*b)*(((24 as int)*a)*a))*d)))))*(a+((a*c)*(d+b))))*((((b*((c*a)*d))*b)*(((((b-b)*(((d*c)*(b*c))*((c*b)-(b*d))))*(c*(c*d)))*(((b*((a+(d*d))*(a+(d*d))))+b)*d))+(((d*(((a*d)*(a*c))*c))-(b+(((a*a)+(c*a))*a)))*(((b*((a+(d*d))*(a+(d*d))))+b)*d))))*((b*((c*b)*((d*((d-(a*b))+((c*c)*(c*b))))*c)))*a)));
	calc !{
		(==)
		temp_26_0;
					{lemma_mul_is_associative(b, b, a);
			lemma_mul_is_distributive((((b-b)*(((d*c)*(b*c))*((c*b)-(b*d))))*(c*(c*d))), ((d*(((a*d)*(a*c))*c))-(b+(((a*a)+(c*a))*a))), (((b*((a+(d*d))*(a+(d*d))))+b)*d));}// 2
		temp_26_2;
	}
	let temp_27_0 = (((((a*b)-((b*((((c*b)+((91 as int)*b))*(a*(d+a)))-b))-((((a*(b*c))*((b*d)*(d*d)))*(((a+a)+b)*((b*b)*a)))*((((c*a)*(a*b))*d)*((d+d)*(24 as int))))))-(((d*a)-(((a*(c*(d-c)))-(c+((b*(39 as int))*(c*a))))*a))*(((((23 as int)*((d*d)*d))-(((d*b)*(b*c))*b))*((((b*a)-(b*a))*a)*(((d*a)*(c+c))*((b*d)*b))))-((d*((d+(a*d))*((a*c)-(d*a))))*((((c+b)-(c*c))*(d*(d*(85 as int))))*(a*d))))))*(b-(((((((b*c)*d)*((c*b)*(c*a)))-((d-(c*c))*((c*d)+(c*a))))*((((b*d)*(b*a))*(c*(c-a)))+(((d*a)*(b*b))*((b*c)*a))))*(((((c*a)*b)+((d*d)*(d*b)))*(((d*d)*b)*((d+b)*(b+a))))*(c*(c*(c-(b*b))))))*(((b*a)*(b*(d*(a-b))))*(a*d)))))*(a*(((((((d*d)*((d+b)-(a*d)))*(((d*b)*(d*c))*((a*a)-(b-b))))+(((a*d)+((b*b)*a))*(((b*c)*(b*d))-c)))*(((b*(c*(23 as int)))*(((a*d)+(d*c))*((a+a)*(d*b))))*((b*((a*c)*(b*c)))*(((b*d)*(c*a))-((b+c)*(d*d))))))*c)*(a*(((b*((c*(a*b))*b))*(a*((c-(a+a))+(c*(d*a)))))*(((((b*a)-d)*d)*c)*b))))));
	let temp_27_2 = (((((a*b)-((b*((((c*b)+((91 as int)*b))*(a*(d+a)))-b))-(((((a*(b*c))*((b*d)*(d*d)))*(((a+a)+b)*((b*b)*a)))*(((c*a)*(a*b))*d))*((d+d)*(24 as int)))))-(((d*a)-(((a*(c*(d-c)))-(c+((b*(39 as int))*(c*a))))*a))*(((((23 as int)*((d*d)*d))-(((d*b)*(b*c))*b))*((((b*a)-(b*a))*a)*(((d*a)*(c+c))*((b*d)*b))))-((d*((d+(a*d))*((a*c)-(d*a))))*((((c+b)*(d*(d*(85 as int))))-((c*c)*(d*(d*(85 as int)))))*(a*d))))))*(b-(((((((b*c)*d)*((c*b)*(c*a)))-((d-(c*c))*((c*d)+(c*a))))*((((b*d)*(b*a))*(c*(c-a)))+(((d*a)*(b*b))*((b*c)*a))))*(((((c*a)*b)+((d*d)*(d*b)))*(((d*d)*b)*((d+b)*(b+a))))*(c*(c*(c-(b*b))))))*(((b*a)*(b*(d*(a-b))))*(a*d)))))*(a*(((((((d*d)*((d+b)-(a*d)))*(((d*b)*(d*c))*((a*a)-(b-b))))+(((a*d)+((b*b)*a))*(((b*c)*(b*d))-c)))*(((b*(c*(23 as int)))*(((a*d)+(d*c))*((a+a)*(d*b))))*((b*((a*c)*(b*c)))*(((b*d)*(c*a))-((b+c)*(d*d))))))*c)*(a*(((b*((c*(a*b))*b))*(a*((c-(a+a))+(c*(d*a)))))*(((((b*a)-d)*d)*c)*b))))));
	calc !{
		(==)
		temp_27_0;
					{lemma_mul_is_associative((((a*(b*c))*((b*d)*(d*d)))*(((a+a)+b)*((b*b)*a))), (((c*a)*(a*b))*d), ((d+d)*(24 as int)));
			lemma_mul_is_distributive((c+b), (c*c), (d*(d*(85 as int))));}// 2
		temp_27_2;
	}
	let temp_28_0 = (((b*b)+(((((d*d)*(((a-(c*d))*((d*c)+(b*d)))*b))*(((33 as int)*c)*((((c*c)*(a*b))*c)*(((d-(93 as int))*c)*c))))*((d*d)*d))*((b*d)*((c*((((d*c)*(b+d))+((c*c)*c))*(((a*d)*(c*c))+((b*d)*(b-c)))))*b))))+(d*c));
	let temp_28_2 = (((b*b)+(((((d*d)*(((a-(c*d))*((d*c)+(b*d)))*b))*(((33 as int)*c)*((((c*c)*(a*b))*c)*(((d-(93 as int))*c)*c))))*((d*d)*d))*((b*d)*((c*((((d*c)*(b+d))+((c*c)*c))*(((a*d)*(c*c))+((b*d)*(b-c)))))*b))))+(d*c));
	calc !{
		(==)
		temp_28_0;
					{lemma_mul_is_distributive((((d*c)*(b+d))+((c*c)*c)), ((a*d)*(c*c)), ((b*d)*(b-c)));
			lemma_mul_is_distributive((((d*c)*(b+d))+((c*c)*c)), ((a*d)*(c*c)), ((b*d)*(b-c)));}// 2
		temp_28_2;
	}
	let temp_29_0 = (((((((a*d)*(a+c))*d)*((((((b-d)+(d*b))*((d*a)*(d*a)))*(d-(a+(c+a))))*((d*d)+b))*(c*(a*a))))*((d*(((((a*d)*a)*(c*(b*a)))*(d*((a*a)*c)))*(((d*b)*c)-d)))*(((b+(a*d))-c)*((((b*(a*c))*(b-(a-(50 as int))))*((c*c)*((a*b)*c)))-c))))*(b*(d*(c*((b*((c+(a+c))*((b*c)*d)))*((d*b)*(((c*a)+d)*(a*(d*a)))))))))*(((a*c)*d)*((((c*c)*c)*(((b*c)*(a*b))*((a+a)*(b*(c*((b-c)*(a-d)))))))-(((a*((a*a)*(((d*d)*(a*d))*((d*d)-(d*c)))))*(((((d*a)*b)+((b-b)+(c*a)))*((a-(a*a))*(a-d)))-(d*(((a*a)*(d*c))*((a*c)*(d*(55 as int)))))))*((((((d+a)*d)*((a+c)*(a*b)))*(((b*a)*(c*b))*a))*((((a+c)*b)*(b*(d+d)))*(b*(c*(a*b)))))*((d*c)*(a*(d*((d*d)*c)))))))));
	let temp_29_2 = (((((((a*d)*(a+c))*d)*((((((b-d)+(d*b))*((d*a)*(d*a)))*(d-(a+(c+a))))*((d*d)+b))*(c*(a*a))))*((d*(((((a*d)*a)*(c*(b*a)))*(d*((a*a)*c)))*(((d*b)*c)-d)))*(((b+(a*d))-c)*(((b*((a*c)*(b-(a-(50 as int)))))*((c*c)*((a*b)*c)))-c))))*(b*(d*(c*((b*((c+(a+c))*((b*c)*d)))*((d*b)*(((c*a)+d)*(a*(d*a)))))))))*(((a*c)*d)*((((c*c)*c)*(((b*c)*(a*b))*((a+a)*(b*(c*((b-c)*(a-d)))))))-(((a*((a*a)*(((d*d)*(a*d))*((d*d)-(d*c)))))*(((((d*a)*b)+((b-b)+(c*a)))*((a*(a-d))-((a*a)*(a-d))))-(d*(((a*a)*(d*c))*((a*c)*(d*(55 as int)))))))*((((((d+a)*d)*((a+c)*(a*b)))*(((b*a)*(c*b))*a))*((((a+c)*b)*(b*(d+d)))*(b*(c*(a*b)))))*((d*c)*(a*(d*((d*d)*c)))))))));
	calc !{
		(==)
		temp_29_0;
					{lemma_mul_is_associative(b, (a*c), (b-(a-(50 as int))));
			lemma_mul_is_distributive(a, (a*a), (a-d));}// 2
		temp_29_2;
	}
	let temp_30_0 = (((((b*(d*((((d+a)*(a*b))*d)*(((a*d)*a)*(c*(a*a))))))*d)*(c*(b+((c*(c-(17 as int)))*((((a*d)*d)*((a*a)*c))*((((25 as int)*a)*(b*c))*((b*d)*(a-b))))))))*d)*((c*a)*((((c*((b*((d+c)*b))*(((b*(13 as int))*b)-((c*a)*(b*d)))))+((d*(((c+c)*(a*c))*((c*d)*c)))-d))*((((((d*b)*(c-b))*(d+(d*a)))*(((d*d)*(c*d))*((d*c)+d)))-((c*(b*(d*a)))*c))*c))*(((b*((((d-b)-d)*((b-d)*b))*a))*a)-((b*((((d+d)*(b*b))*(c*c))*(a*(a*a))))+(d*(d*(((a*c)*b)*(b*(b*a))))))))));
	let temp_30_2 = (((((b*(d*((((d+a)*(a*b))*d)*(((a*d)*a)*(c*(a*a))))))*d)*(c*(b+((c*(c-(17 as int)))*((((a*d)*d)*((a*a)*c))*((((25 as int)*a)*(b*c))*((b*d)*(a-b))))))))*d)*((c*a)*((((c*(((b*((d+c)*b))*((b*(13 as int))*b))-((b*((d+c)*b))*((c*a)*(b*d)))))+((d*(((c+c)*(a*c))*((c*d)*c)))-d))*((((((d*b)*(c-b))*(d+(d*a)))*(((d*d)*(c*d))*((d*c)+d)))-((c*(b*(d*a)))*c))*c))*(((b*((((d-b)-d)*((b-d)*b))*a))*a)-((b*((((d+d)*(b*b))*(c*c))*((a*a)*a)))+(d*(d*(((a*c)*b)*(b*(b*a))))))))));
	calc !{
		(==)
		temp_30_0;
					{lemma_mul_is_distributive((b*((d+c)*b)), ((b*(13 as int))*b), ((c*a)*(b*d)));
			lemma_mul_is_commutative(a, (a*a));}// 2
		temp_30_2;
	}
	let temp_31_0 = (((((c-((b*(((d*d)*d)*((a*c)-(b*b))))*c))*(a*d))*((a*(((a+((c*c)-(c*b)))*((c*b)*c))*((a*(b-c))*(((d*b)*(b*d))*((d*c)+b)))))*c))-((b*(((b*(d*((b+d)*d)))*c)*((c*((c*c)+((a*b)*(a*c))))*b)))*((((b+b)-(c*((c*c)+d)))*c)*(((c*(((d*a)+(d*a))*c))*(((a*(b*c))*(d*(c*(96 as int))))*(b*((d*a)*c))))*(d+(((d*c)*d)*b))))))*((((c+c)+d)-((d*a)*a))-((((a*(d*(d+d)))*b)+((c+((b*d)*c))*(((((d-b)-c)*((a*d)*b))*d)-(a*a))))-((c-((b*(a*((a*a)+d)))*(d+(((c*b)*(d*a))*(b*((14 as int)*c))))))*a))));
	let temp_31_2 = (((((c-((b*(((d*d)*d)*((a*c)-(b*b))))*c))*(a*d))*((a*(((a+(c*(c-b)))*((c*b)*c))*((a*(b-c))*(((d*b)*(b*d))*((d*c)+b)))))*c))-((b*(((b*(d*((b+d)*d)))*c)*((c*((c*c)+((a*b)*(a*c))))*b)))*((((b+b)-(c*((c*c)+d)))*c)*(((c*((d*(a+a))*c))*(((a*(b*c))*(d*(c*(96 as int))))*(b*((d*a)*c))))*(d+(((d*c)*d)*b))))))*((((c+c)+d)-((d*a)*a))-((((a*(d*(d+d)))*b)+((c+((b*d)*c))*(((((d-b)-c)*((a*d)*b))*d)-(a*a))))-((c-((b*(a*((a*a)+d)))*(d+(((c*b)*(d*a))*(b*((14 as int)*c))))))*a))));
	calc !{
		(==)
		temp_31_0;
					{lemma_mul_is_distributive(d, a, a);
			lemma_mul_is_distributive(c, c, b);}// 2
		temp_31_2;
	}
	let temp_32_0 = ((a*b)+(a*(b*((((((d*b)-(d*b))*((a*d)*d))*(d*((d*c)*((c*d)*(a*c)))))*c)*(((d-(((c*c)*(1 as int))*d))*c)*(b*a))))));
	let temp_32_2 = ((a*b)+(a*(b*(((((((d*b)-(d*b))*((a*d)*d))*(d*((d*c)*(c*(d*(a*c))))))*c)*((d-(((c*c)*(1 as int))*d))*c))*(b*a)))));
	calc !{
		(==)
		temp_32_0;
					{lemma_mul_is_associative(c, d, (a*c));
			lemma_mul_is_associative((((((d*b)-(d*b))*((a*d)*d))*(d*((d*c)*((c*d)*(a*c)))))*c), ((d-(((c*c)*(1 as int))*d))*c), (b*a));}// 2
		temp_32_2;
	}
	let temp_33_0 = (((d*((d*((((a*b)*((b*b)*(c*c)))*(((b*b)*c)*c))*((d*(c*(d*a)))*(((d*c)*(b+(43 as int)))+((b*d)+d)))))*b))*(22 as int))*(b*(((d+((((d+(d*a))*d)*(89 as int))*c))*a)+(c-(b*b)))));
	let temp_33_2 = (((d*((d*((((a*b)*((b*b)*(c*c)))*(((b*b)*c)*c))*((d*(c*(d*a)))*(((d*c)*(b+(43 as int)))+((b*d)+d)))))*b))*(22 as int))*((b*((d+((((d*d)+((d*a)*d))*(89 as int))*c))*a))+(b*(c-(b*b)))));
	calc !{
		(==)
		temp_33_0;
					{lemma_mul_is_distributive(b, ((d+((((d*d)+((d*a)*d))*(89 as int))*c))*a), (c-(b*b)));
			lemma_mul_is_distributive(d, (d*a), d);}// 2
		temp_33_2;
	}
	let temp_34_0 = ((((a*(b*c))*c)*(((((c*(((b+a)*(a-c))*((d*b)+(b*d))))*a)*c)*((((a*(d*(c*b)))*((a*a)*((d*a)-(d*c))))*c)*a))*(((c*(b*b))*(((((c*(69 as int))*d)*c)*(d*((c*c)-(c*d))))*((((a*c)*(a*b))*(b*(b*d)))*(((a*d)-d)*((b*d)*d)))))*(c*((b*c)-(b*(((d+d)+(b+b))*((c*a)*d))))))))*(((d*a)*b)*(((((((c*(b*a))*((b*c)*(a*b)))*((b*(b*d))*c))*((d*((b+d)*(c*c)))+((b*(c*c))-((d*d)*(c*c)))))*((a*(c*((a*c)*(b*a))))*(b*(((a*b)*(b*b))*((b*c)-b)))))*((b*((a*(d+(d*c)))*(b*(c*(b+c)))))*(d*((c*((b*b)*(a*d)))*d))))*(((((d*((a+b)*(c*b)))*((a*(a*d))*(a*(d*c))))*c)*(((c*((d*d)*(b*c)))*c)*c))*((((a*((c*c)*((31 as int)*d)))*(65 as int))*((((b*c)*d)*((c*a)*(b*c)))*c))*(((((d*b)*(c*(92 as int)))*b)-((b*(a*d))*d))*((((b*c)*(b*d))*((c-c)*(a*b)))*b)))))));
	let temp_34_2 = ((((a*(b*c))*c)*(((((c*(((b+a)*(a-c))*((d*b)+(b*d))))*a)*c)*((((a*(d*(c*b)))*((a*a)*((d*a)-(d*c))))*c)*a))*(((c*(b*b))*(((((c*(69 as int))*d)*c)*(d*((c*c)-(c*d))))*((((a*c)*(a*b))*(b*(b*d)))*(((a*d)-d)*((b*d)*d)))))*(c*((b*c)-(b*(((d+d)+(b+b))*((c*a)*d))))))))*(((d*a)*b)*(((((((c*(b*a))*((b*c)*(a*b)))*((b*(b*d))*c))*((d*((b+d)*(c*c)))+((b*(c*c))-((d*d)*(c*c)))))*((a*(c*((a*c)*(b*a))))*((b*((a*b)*(b*b)))*((b*c)-b))))*((b*((a*(d+(d*c)))*(b*(c*(b+c)))))*(d*((c*((b*b)*(a*d)))*d))))*(((((d*((a+b)*(c*b)))*((a*(a*d))*(a*(d*c))))*c)*(((c*((d*d)*(b*c)))*c)*c))*((((a*((c*c)*((31 as int)*d)))*(65 as int))*((((b*c)*d)*((c*a)*(b*c)))*c))*(((((d*b)*(c*(92 as int)))*b)-((b*(a*d))*d))*(((b*c)*(b*d))*(((c-c)*(a*b))*b))))))));
	calc !{
		(==)
		temp_34_0;
					{lemma_mul_is_associative(((b*c)*(b*d)), ((c-c)*(a*b)), b);
			lemma_mul_is_associative(b, ((a*b)*(b*b)), ((b*c)-b));}// 2
		temp_34_2;
	}
	let temp_35_0 = ((d*((c*(((d*a)*(a*(c*((d+b)*a))))+((d*(b+(a*a)))*c)))*(((((((c*c)-(c*d))*((a*a)*(c+c)))*(((d*d)*d)*((a*a)*(75 as int))))*b)*((a*(a*a))*(b*(((c+d)+(a*d))*b))))+(((b*(((c*c)*d)*d))*(a*c))*(((((d+c)*a)*d)+(((d*a)*(b*b))*((b*c)*c)))-(b*a))))))-c);
	let temp_35_2 = ((d*((c*(((d*a)*(a*(c*((d+b)*a))))+((d*(b+(a*a)))*c)))*((((((c*(c-d))*((a*a)*(c+c)))*(((d*d)*d)*((a*a)*(75 as int))))*b)*((a*(a*a))*(b*(((c+d)+(a*d))*b))))+(((b*((c*(c*d))*d))*(a*c))*(((((d+c)*a)*d)+(((d*a)*(b*b))*((b*c)*c)))-(b*a))))))-c);
	calc !{
		(==)
		temp_35_0;
					{lemma_mul_is_associative(c, c, d);
			lemma_mul_is_distributive(c, c, d);}// 2
		temp_35_2;
	}
	let temp_36_0 = (((((d*d)-d)*((d*(((((b-a)*(b*(20 as int)))*((a*b)+(b*b)))-(((b-c)*(c-b))*(c+(a*b))))*((((d*a)-c)+((c*b)*(d+a)))+(((c*c)*((73 as int)*a))*((b*d)-d)))))*(a+((d*(((c*a)*(d*a))*((d*d)*(d-(18 as int)))))*((((c*c)*a)*a)*((a*a)*a))))))*(d-((((((b*(a*c))*((a*c)-(b+a)))*(((d*d)*(c*c))+(c+(a*b))))*c)*(d*((b*((a*c)*(c-b)))*((d*(c*d))*d))))*((((98 as int)*(d*d))*((d*((c*a)*(c*b)))+(d*((a+d)*(a*b)))))*(((a*((a-a)-(c*a)))*(((a*b)*(d*d))*(b*(a*d))))*((((b+a)-(d*d))*((b*a)*(b*c)))*(((c*b)*(b*b))*((b*b)*(a*a)))))))))*c);
	let temp_36_2 = (((((d*d)-d)*((d*(((((b-a)*(b*(20 as int)))*((a*b)+(b*b)))*((((d*a)-c)+((c*b)*(d+a)))+(((c*c)*((73 as int)*a))*((b*d)-d))))-((((b-c)*(c-b))*(c+(a*b)))*((((d*a)-c)+((c*b)*(d+a)))+(((c*c)*((73 as int)*a))*((b*d)-d))))))*(a+((d*(((c*a)*(d*a))*((d*d)*(d-(18 as int)))))*((((c*c)*a)*a)*((a*a)*a))))))*(d-((((((b*(a*c))*((a*c)-(b+a)))*(((d*d)*(c*c))+(c+(a*b))))*c)*(d*((b*((a*c)*(c-b)))*(((c*d)*d)*d))))*((((98 as int)*(d*d))*((d*((c*a)*(c*b)))+(d*((a+d)*(a*b)))))*(((a*((a-a)-(c*a)))*(((a*b)*(d*d))*(b*(a*d))))*((((b+a)-(d*d))*((b*a)*(b*c)))*(((c*b)*(b*b))*((b*b)*(a*a)))))))))*c);
	calc !{
		(==)
		temp_36_0;
					{lemma_mul_is_commutative(d, (c*d));
			lemma_mul_is_distributive((((b-a)*(b*(20 as int)))*((a*b)+(b*b))), (((b-c)*(c-b))*(c+(a*b))), ((((d*a)-c)+((c*b)*(d+a)))+(((c*c)*((73 as int)*a))*((b*d)-d))));}// 2
		temp_36_2;
	}
	let temp_37_0 = (((d*((d*((c*a)*((a*((a*a)*(d*d)))*(c+((d*a)*d)))))*b))*a)*(c*c));
	let temp_37_2 = (((d*((d*(((c*a)*((a*((a*a)*(d*d)))*c))+((c*a)*((a*((a*a)*(d*d)))*((d*a)*d)))))*b))*a)*(c*c));
	calc !{
		(==)
		temp_37_0;
					{lemma_mul_is_distributive((c*a), ((a*((a*a)*(d*d)))*c), ((a*((a*a)*(d*d)))*((d*a)*d)));
			lemma_mul_is_distributive((a*((a*a)*(d*d))), c, ((d*a)*d));}// 2
		temp_37_2;
	}
	let temp_38_0 = (((((((((a*(a-a))*((d*d)+(b*a)))*((b*(d*a))+(a*d)))*((((b*a)*d)*c)*(d*(d+d))))*((a*((((0 as int)*a)-(c*a))*((c*a)*(a*d))))*d))*d)*b)*b)*((c-((((((a-d)*((d*b)*(b*b)))*(((b*c)*c)*((a*b)-(a+a))))*(c*((d*a)-d)))*(c*(b-b)))*((((((b*d)*(c+c))*((a*c)-d))+(((d*c)*(d*d))*(d*c)))*(((a*(a*a))*b)*((b*(b*a))-((b+d)*a))))*(d*d))))*((((((((d*a)-(b*a))*(c*(b*b)))*b)*((((a+a)*(a*c))-((b*b)*b))*(b*((d*c)*(d*(18 as int))))))*((((b*(b*a))*a)-d)+((b*((d*d)*b))-c)))*b)*(((d*(((b-(d*a))*(c*(d*a)))*d))*c)+((((b-d)*(b*(d*c)))*(((b*(c*d))*a)*(((b*c)*a)*(d*(c*a)))))+(d*c))))));
	let temp_38_2 = (((((((((a*(a-a))*((d*d)+(b*a)))*((b*(d*a))+(a*d)))*((d*(d+d))*(((b*a)*d)*c)))*((a*((((0 as int)*a)-(c*a))*((c*a)*(a*d))))*d))*d)*b)*b)*((c-((((((a-d)*((d*b)*(b*b)))*(((b*c)*c)*((a*b)-(a+a))))*(c*((d*a)-d)))*(c*(b-b)))*((((((b*d)*(c+c))*((a*c)-d))+(((d*c)*(d*d))*(d*c)))*(((a*(a*a))*b)*((b*(b*a))-((b+d)*a))))*(d*d))))*((((((((d*a)-(b*a))*(c*(b*b)))*b)*(((((a+a)*a)*c)-((b*b)*b))*(b*((d*c)*(d*(18 as int))))))*((((b*(b*a))*a)-d)+((b*((d*d)*b))-c)))*b)*(((d*(((b-(d*a))*(c*(d*a)))*d))*c)+((((b-d)*(b*(d*c)))*(((b*(c*d))*a)*(((b*c)*a)*(d*(c*a)))))+(d*c))))));
	calc !{
		(==)
		temp_38_0;
					{lemma_mul_is_commutative((((b*a)*d)*c), (d*(d+d)));
			lemma_mul_is_associative((a+a), a, c);}// 2
		temp_38_2;
	}
	let temp_39_0 = ((((b*b)*d)*c)*(d+((c-c)*((((((a*(b+c))*c)*(((c*d)-(d*a))*a))*((b*((b*d)*(b*d)))*(d+b)))*((b*(((d-b)*(b*d))*b))+((d*b)+(((c*d)*(a*d))*(a*(c-d))))))*a))));
	let temp_39_2 = ((((b*b)*d)*c)*(d+((c-c)*((((b*(((d-b)*(b*d))*b))+((d*b)+(((c*d)*(a*d))*((c-d)*a))))*((((a*(b+c))*c)*(((c*d)-(d*a))*a))*((b*((b*d)*(b*d)))*(d+b))))*a))));
	calc !{
		(==)
		temp_39_0;
					{lemma_mul_is_commutative(a, (c-d));
			lemma_mul_is_commutative(((((a*(b+c))*c)*(((c*d)-(d*a))*a))*((b*((b*d)*(b*d)))*(d+b))), ((b*(((d-b)*(b*d))*b))+((d*b)+(((c*d)*(a*d))*(a*(c-d))))));}// 2
		temp_39_2;
	}

}
} // verus!