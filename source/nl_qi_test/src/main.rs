use builtin_macros::*;
use builtin::*;
use vstd::calc_macro::*;
mod nl_basics;
use nl_basics::*;

verus! {
 #[verifier::spinoff_prover]
pub proof fn calc_algebra_inst_hint(a: int,b: int,c: int)
{
	calc !{
		(==)
		(((((b-b)-(c+a))-((a*c)*(b*a)))+(((c*a)*(b*c))+((a+a)*(b*b))))*((((c+b)*(a*c))*((c*a)-(a+c)))*(((c*a)*(c*c))*((36+c)*(a-c)))));
			{lemma_mul_is_commutative((c*a), (c*c)); assert(((c*a)*(c*c)) == ((c*c)*(c*a)));}
		(((((b-b)-(c+a))-((a*c)*(b*a)))+(((c*a)*(b*c))+((a+a)*(b*b))))*((((c+b)*(a*c))*((c*a)-(a+c)))*(((c*c)*(c*a))*((36+c)*(a-c)))));
			{lemma_mul_add_is_right_distributive(36, c, (a-c)); assert(((36+c)*(a-c)) == ((36*(a-c))+(c*(a-c))));}
		(((((b-b)-(c+a))-((a*c)*(b*a)))+(((c*a)*(b*c))+((a+a)*(b*b))))*((((c+b)*(a*c))*((c*a)-(a+c)))*(((c*c)*(c*a))*((36*(a-c))+(c*(a-c))))));
			{lemma_mul_sub_is_left_distributive(c, a, c); assert((c*(a-c)) == ((c*a)-(c*c)));}
		(((((b-b)-(c+a))-((a*c)*(b*a)))+(((c*a)*(b*c))+((a+a)*(b*b))))*((((c+b)*(a*c))*((c*a)-(a+c)))*(((c*c)*(c*a))*((36*(a-c))+((c*a)-(c*c))))));
			{lemma_mul_is_commutative(c, a); assert((c*a) == (a*c));}
		(((((b-b)-(c+a))-((a*c)*(b*a)))+(((c*a)*(b*c))+((a+a)*(b*b))))*((((c+b)*(a*c))*((a*c)-(a+c)))*(((c*c)*(c*a))*((36*(a-c))+((c*a)-(c*c))))));
			{lemma_mul_add_is_right_distributive((((b-b)-(c+a))-((a*c)*(b*a))), (((c*a)*(b*c))+((a+a)*(b*b))), ((((c+b)*(a*c))*((a*c)-(a+c)))*(((c*c)*(c*a))*((36*(a-c))+((c*a)-(c*c)))))); assert((((((b-b)-(c+a))-((a*c)*(b*a)))+(((c*a)*(b*c))+((a+a)*(b*b))))*((((c+b)*(a*c))*((a*c)-(a+c)))*(((c*c)*(c*a))*((36*(a-c))+((c*a)-(c*c)))))) == (((((b-b)-(c+a))-((a*c)*(b*a)))*((((c+b)*(a*c))*((a*c)-(a+c)))*(((c*c)*(c*a))*((36*(a-c))+((c*a)-(c*c))))))+((((c*a)*(b*c))+((a+a)*(b*b)))*((((c+b)*(a*c))*((a*c)-(a+c)))*(((c*c)*(c*a))*((36*(a-c))+((c*a)-(c*c))))))));}
		(((((b-b)-(c+a))-((a*c)*(b*a)))*((((c+b)*(a*c))*((a*c)-(a+c)))*(((c*c)*(c*a))*((36*(a-c))+((c*a)-(c*c))))))+((((c*a)*(b*c))+((a+a)*(b*b)))*((((c+b)*(a*c))*((a*c)-(a+c)))*(((c*c)*(c*a))*((36*(a-c))+((c*a)-(c*c)))))));
			{lemma_mul_is_commutative((((c*a)*(b*c))+((a+a)*(b*b))), ((((c+b)*(a*c))*((a*c)-(a+c)))*(((c*c)*(c*a))*((36*(a-c))+((c*a)-(c*c)))))); assert(((((c*a)*(b*c))+((a+a)*(b*b)))*((((c+b)*(a*c))*((a*c)-(a+c)))*(((c*c)*(c*a))*((36*(a-c))+((c*a)-(c*c)))))) == (((((c+b)*(a*c))*((a*c)-(a+c)))*(((c*c)*(c*a))*((36*(a-c))+((c*a)-(c*c)))))*(((c*a)*(b*c))+((a+a)*(b*b)))));}
		(((((b-b)-(c+a))-((a*c)*(b*a)))*((((c+b)*(a*c))*((a*c)-(a+c)))*(((c*c)*(c*a))*((36*(a-c))+((c*a)-(c*c))))))+(((((c+b)*(a*c))*((a*c)-(a+c)))*(((c*c)*(c*a))*((36*(a-c))+((c*a)-(c*c)))))*(((c*a)*(b*c))+((a+a)*(b*b)))));
			{lemma_mul_is_associative((c+b), a, c); assert(((c+b)*(a*c)) == (((c+b)*a)*c));}
		(((((b-b)-(c+a))-((a*c)*(b*a)))*(((((c+b)*a)*c)*((a*c)-(a+c)))*(((c*c)*(c*a))*((36*(a-c))+((c*a)-(c*c))))))+((((((c+b)*a)*c)*((a*c)-(a+c)))*(((c*c)*(c*a))*((36*(a-c))+((c*a)-(c*c)))))*(((c*a)*(b*c))+((a+a)*(b*b)))));
			{lemma_mul_is_associative(((((c+b)*a)*c)*((a*c)-(a+c))), (((c*c)*(c*a))*((36*(a-c))+((c*a)-(c*c)))), (((c*a)*(b*c))+((a+a)*(b*b)))); assert(((((((c+b)*a)*c)*((a*c)-(a+c)))*(((c*c)*(c*a))*((36*(a-c))+((c*a)-(c*c)))))*(((c*a)*(b*c))+((a+a)*(b*b)))) == (((((c+b)*a)*c)*((a*c)-(a+c)))*((((c*c)*(c*a))*((36*(a-c))+((c*a)-(c*c))))*(((c*a)*(b*c))+((a+a)*(b*b))))));}
		(((((b-b)-(c+a))-((a*c)*(b*a)))*(((((c+b)*a)*c)*((a*c)-(a+c)))*(((c*c)*(c*a))*((36*(a-c))+((c*a)-(c*c))))))+(((((c+b)*a)*c)*((a*c)-(a+c)))*((((c*c)*(c*a))*((36*(a-c))+((c*a)-(c*c))))*(((c*a)*(b*c))+((a+a)*(b*b))))));
			{lemma_mul_sub_is_left_distributive(36, a, c); assert((36*(a-c)) == ((36*a)-(36*c)));}
		(((((b-b)-(c+a))-((a*c)*(b*a)))*(((((c+b)*a)*c)*((a*c)-(a+c)))*(((c*c)*(c*a))*(((36*a)-(36*c))+((c*a)-(c*c))))))+(((((c+b)*a)*c)*((a*c)-(a+c)))*((((c*c)*(c*a))*(((36*a)-(36*c))+((c*a)-(c*c))))*(((c*a)*(b*c))+((a+a)*(b*b))))));
			{lemma_mul_is_associative((c*c), c, a); assert(((c*c)*(c*a)) == (((c*c)*c)*a));}
		(((((b-b)-(c+a))-((a*c)*(b*a)))*(((((c+b)*a)*c)*((a*c)-(a+c)))*((((c*c)*c)*a)*(((36*a)-(36*c))+((c*a)-(c*c))))))+(((((c+b)*a)*c)*((a*c)-(a+c)))*(((((c*c)*c)*a)*(((36*a)-(36*c))+((c*a)-(c*c))))*(((c*a)*(b*c))+((a+a)*(b*b))))));
	}
}

fn main() {
}

} // verus!
