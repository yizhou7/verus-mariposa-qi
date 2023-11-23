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
		(((b+b)*(a*8))*((c*a)*(a*a)));
			{lemma_mul_is_associative((b+b), a, 8); assert(((b+b)*(a*8)) == (((b+b)*a)*8));}
		((((b+b)*a)*8)*((c*a)*(a*a)));
			{lemma_mul_is_associative(((b+b)*a), 8, ((c*a)*(a*a))); assert(((((b+b)*a)*8)*((c*a)*(a*a))) == ((((b+b)*a)*8)*((c*a)*(a*a))));}
		((((b+b)*a)*8)*((c*a)*(a*a)));
			{lemma_mul_is_commutative((((b+b)*a)*8), ((c*a)*(a*a))); assert(((((b+b)*a)*8)*((c*a)*(a*a))) == (((c*a)*(a*a))*(((b+b)*a)*8)));}
		(((c*a)*(a*a))*(((b+b)*a)*8));
			{lemma_mul_is_associative(c, a, (a*a)); assert(((c*a)*(a*a)) == ((c*a)*(a*a)));}
		(((c*a)*(a*a))*(((b+b)*a)*8));
			{lemma_mul_is_commutative(a, a); assert((a*a) == (a*a));}
		(((c*a)*(a*a))*(((b+b)*a)*8));
			{lemma_mul_add_is_distributive(b, b, a); assert(((b+b)*a) == ((b*a)+(b*a)));}
		(((c*a)*(a*a))*(((b*a)+(b*a))*8));
			{lemma_mul_is_associative((c*a), a, a); assert(((c*a)*(a*a)) == (((c*a)*a)*a));}
		((((c*a)*a)*a)*(((b*a)+(b*a))*8));
			{lemma_mul_is_commutative((c*a), a); assert(((c*a)*a) == (a*(c*a)));}
		(((a*(c*a))*a)*(((b*a)+(b*a))*8));
			{lemma_mul_is_associative(a, c, a); assert((a*(c*a)) == ((a*c)*a));}
		((((a*c)*a)*a)*(((b*a)+(b*a))*8));
			{lemma_mul_is_commutative((a*c), a); assert(((a*c)*a) == (a*(a*c)));}
		(((a*(a*c))*a)*(((b*a)+(b*a))*8));
	}
}

 #[verifier::spinoff_prover]
pub proof fn calc_algebra_inst_only(a: int,b: int,c: int)
{
	calc !{
		(==)
		(((b+b)*(a*8))*((c*a)*(a*a)));
			{lemma_mul_is_associative((b+b), a, 8);}
		((((b+b)*a)*8)*((c*a)*(a*a)));
			{lemma_mul_is_associative(((b+b)*a), 8, ((c*a)*(a*a)));}
		((((b+b)*a)*8)*((c*a)*(a*a)));
			{lemma_mul_is_commutative((((b+b)*a)*8), ((c*a)*(a*a)));}
		(((c*a)*(a*a))*(((b+b)*a)*8));
			{lemma_mul_is_associative(c, a, (a*a));}
		(((c*a)*(a*a))*(((b+b)*a)*8));
			{lemma_mul_is_commutative(a, a);}
		(((c*a)*(a*a))*(((b+b)*a)*8));
			{lemma_mul_add_is_distributive(b, b, a);}
		(((c*a)*(a*a))*(((b*a)+(b*a))*8));
			{lemma_mul_is_associative((c*a), a, a);}
		((((c*a)*a)*a)*(((b*a)+(b*a))*8));
			{lemma_mul_is_commutative((c*a), a);}
		(((a*(c*a))*a)*(((b*a)+(b*a))*8));
			{lemma_mul_is_associative(a, c, a);}
		((((a*c)*a)*a)*(((b*a)+(b*a))*8));
			{lemma_mul_is_commutative((a*c), a);}
		(((a*(a*c))*a)*(((b*a)+(b*a))*8));
	}
}

 #[verifier::spinoff_prover]
pub proof fn calc_algebra_auto_hint(a: int,b: int,c: int)
{
	calc !{
		(==)
		(((b+b)*(a*8))*((c*a)*(a*a)));
			{lemma_mul_is_associative_auto(); assert(((b+b)*(a*8)) == (((b+b)*a)*8));}
		((((b+b)*a)*8)*((c*a)*(a*a)));
			{lemma_mul_is_associative_auto(); assert(((((b+b)*a)*8)*((c*a)*(a*a))) == ((((b+b)*a)*8)*((c*a)*(a*a))));}
		((((b+b)*a)*8)*((c*a)*(a*a)));
			{lemma_mul_is_commutative_auto(); assert(((((b+b)*a)*8)*((c*a)*(a*a))) == (((c*a)*(a*a))*(((b+b)*a)*8)));}
		(((c*a)*(a*a))*(((b+b)*a)*8));
			{lemma_mul_is_associative_auto(); assert(((c*a)*(a*a)) == ((c*a)*(a*a)));}
		(((c*a)*(a*a))*(((b+b)*a)*8));
			{lemma_mul_is_commutative_auto(); assert((a*a) == (a*a));}
		(((c*a)*(a*a))*(((b+b)*a)*8));
			{lemma_mul_add_is_distributive_auto(); assert(((b+b)*a) == ((b*a)+(b*a)));}
		(((c*a)*(a*a))*(((b*a)+(b*a))*8));
			{lemma_mul_is_associative_auto(); assert(((c*a)*(a*a)) == (((c*a)*a)*a));}
		((((c*a)*a)*a)*(((b*a)+(b*a))*8));
			{lemma_mul_is_commutative_auto(); assert(((c*a)*a) == (a*(c*a)));}
		(((a*(c*a))*a)*(((b*a)+(b*a))*8));
			{lemma_mul_is_associative_auto(); assert((a*(c*a)) == ((a*c)*a));}
		((((a*c)*a)*a)*(((b*a)+(b*a))*8));
			{lemma_mul_is_commutative_auto(); assert(((a*c)*a) == (a*(a*c)));}
		(((a*(a*c))*a)*(((b*a)+(b*a))*8));
	}
}

 #[verifier::spinoff_prover]
pub proof fn calc_algebra_auto_only(a: int,b: int,c: int)
{
	calc !{
		(==)
		(((b+b)*(a*8))*((c*a)*(a*a)));
			{lemma_mul_is_associative_auto();}
		((((b+b)*a)*8)*((c*a)*(a*a)));
			{lemma_mul_is_associative_auto();}
		((((b+b)*a)*8)*((c*a)*(a*a)));
			{lemma_mul_is_commutative_auto();}
		(((c*a)*(a*a))*(((b+b)*a)*8));
			{lemma_mul_is_associative_auto();}
		(((c*a)*(a*a))*(((b+b)*a)*8));
			{lemma_mul_is_commutative_auto();}
		(((c*a)*(a*a))*(((b+b)*a)*8));
			{lemma_mul_add_is_distributive_auto();}
		(((c*a)*(a*a))*(((b*a)+(b*a))*8));
			{lemma_mul_is_associative_auto();}
		((((c*a)*a)*a)*(((b*a)+(b*a))*8));
			{lemma_mul_is_commutative_auto();}
		(((a*(c*a))*a)*(((b*a)+(b*a))*8));
			{lemma_mul_is_associative_auto();}
		((((a*c)*a)*a)*(((b*a)+(b*a))*8));
			{lemma_mul_is_commutative_auto();}
		(((a*(a*c))*a)*(((b*a)+(b*a))*8));
	}
}

pub proof fn calc_algebra_nl_arith_hint(a: int,b: int,c: int) by (nonlinear_arith)
{
	calc !{
		(==)
		(((b+b)*(a*8))*((c*a)*(a*a)));
			{assert(((b+b)*(a*8)) == (((b+b)*a)*8));}
		((((b+b)*a)*8)*((c*a)*(a*a)));
			{assert(((((b+b)*a)*8)*((c*a)*(a*a))) == ((((b+b)*a)*8)*((c*a)*(a*a))));}
		((((b+b)*a)*8)*((c*a)*(a*a)));
			{assert(((((b+b)*a)*8)*((c*a)*(a*a))) == (((c*a)*(a*a))*(((b+b)*a)*8)));}
		(((c*a)*(a*a))*(((b+b)*a)*8));
			{assert(((c*a)*(a*a)) == ((c*a)*(a*a)));}
		(((c*a)*(a*a))*(((b+b)*a)*8));
			{assert((a*a) == (a*a));}
		(((c*a)*(a*a))*(((b+b)*a)*8));
			{assert(((b+b)*a) == ((b*a)+(b*a)));}
		(((c*a)*(a*a))*(((b*a)+(b*a))*8));
			{assert(((c*a)*(a*a)) == (((c*a)*a)*a));}
		((((c*a)*a)*a)*(((b*a)+(b*a))*8));
			{assert(((c*a)*a) == (a*(c*a)));}
		(((a*(c*a))*a)*(((b*a)+(b*a))*8));
			{assert((a*(c*a)) == ((a*c)*a));}
		((((a*c)*a)*a)*(((b*a)+(b*a))*8));
			{assert(((a*c)*a) == (a*(a*c)));}
		(((a*(a*c))*a)*(((b*a)+(b*a))*8));
	}
}

pub proof fn calc_algebra_nl_arith_only(a: int,b: int,c: int) by (nonlinear_arith)
{
	calc !{
		(==)
		(((b+b)*(a*8))*((c*a)*(a*a)));
			{}
		((((b+b)*a)*8)*((c*a)*(a*a)));
			{}
		((((b+b)*a)*8)*((c*a)*(a*a)));
			{}
		(((c*a)*(a*a))*(((b+b)*a)*8));
			{}
		(((c*a)*(a*a))*(((b+b)*a)*8));
			{}
		(((c*a)*(a*a))*(((b+b)*a)*8));
			{}
		(((c*a)*(a*a))*(((b*a)+(b*a))*8));
			{}
		((((c*a)*a)*a)*(((b*a)+(b*a))*8));
			{}
		(((a*(c*a))*a)*(((b*a)+(b*a))*8));
			{}
		((((a*c)*a)*a)*(((b*a)+(b*a))*8));
			{}
		(((a*(a*c))*a)*(((b*a)+(b*a))*8));
	}
}

fn main() {
}

} // verus!
