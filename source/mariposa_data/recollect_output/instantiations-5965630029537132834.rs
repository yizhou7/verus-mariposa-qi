use builtin_macros::*;
// use builtin::*;
mod nl_basics;
use crate::nl_basics::*;
verus! {

pub proof fn free_0(a: Elem, b: Elem, c: Elem, d: Elem, m: Elem)
{
	let temp_0_0 = (mul_((mul_(c, c)), (mul_(c, b))));
	let temp_0_1 = (mul_((mul_((mul_(c, c)), c)), b));
	assert(eq_(temp_0_0, temp_0_1)) by {
		lemma_mul_assoc(mul_(c, c), c, b);
	}
	let temp_1_0 = (mul_((mul_((mod_(b, m)), a)), (mul_(b, (mod_(b, m))))));
	let temp_1_1 = (mul_((mod_(b, m)), (mul_(a, (mul_(b, (mod_(b, m))))))));
	assert(eq_(temp_1_0, temp_1_1)) by {
		lemma_eq_sym(temp_1_1, temp_1_0);
		lemma_mul_assoc(mod_(b, m), a, mul_(b, mod_(b, m)));
	}
	let temp_2_0 = (mul_((mul_(b, d)), (sub_(d, d))));
	let temp_2_1 = (mul_(b, (mul_(d, (sub_(d, d))))));
	assert(eq_(temp_2_0, temp_2_1)) by {
		lemma_eq_sym(temp_2_1, temp_2_0);
		lemma_mul_assoc(b, d, sub_(d, d));
	}
	let temp_3_0 = (mul_((mul_((mod_(a, m)), d)), (mul_(b, a))));
	let temp_3_1 = (mul_((mul_(b, a)), (mul_((mod_(a, m)), d))));
	assert(eq_(temp_3_0, temp_3_1)) by {
		lemma_mul_comm(mul_(mod_(a, m), d), mul_(b, a));
	}
	let temp_4_0 = (mul_((add_(c, a)), (mul_(a, b))));
	let temp_4_1 = (add_((mul_(c, (mul_(a, b)))), (mul_(a, (mul_(a, b))))));
	assert(eq_(temp_4_0, temp_4_1)) by {
		lemma_mul_dist(c, a, mul_(a, b));
	}
	let temp_5_0 = (sub_((mul_(d, c)), (mul_(b, (mod_(a, m))))));
	let temp_5_1 = (sub_((mul_(d, c)), (mul_(b, (mod_((add_(a, (mul_((add_((mul_(a, c)), (mod_((mul_(a, (mod_(c, m)))), m)))), m)))), m))))));
	assert(eq_(temp_5_0, temp_5_1)) by {
		lemma_mod_mul_vanish(a, add_(mul_(a, c), mod_(mul_(a, mod_(c, m)), m)), m);
		cong_sub_(mul_(d, c), mul_(b, mod_(a, m)), mul_(d, c), mul_(b, mod_(add_(a, mul_(add_(mul_(a, c), mod_(mul_(a, mod_(c, m)), m)), m)), m)));
		lemma_eq_ref(b);
		lemma_eq_ref(mul_(d, c));
		cong_mul_(b, mod_(a, m), b, mod_(add_(a, mul_(add_(mul_(a, c), mod_(mul_(a, mod_(c, m)), m)), m)), m));
	}
	let temp_6_0 = (add_((mul_(d, b)), (mul_(b, a))));
	let temp_6_1 = (add_((mul_(b, d)), (mul_(b, a))));
	assert(eq_(temp_6_0, temp_6_1)) by {
		cong_add_(mul_(d, b), mul_(b, a), mul_(b, d), mul_(b, a));
		lemma_mul_comm(d, b);
		lemma_eq_ref(mul_(b, a));
	}
	let temp_7_0 = (mod_((mul_((add_(a, a)), (mul_(d, b)))), m));
	let temp_7_1 = (mod_((mul_((mul_((add_(a, a)), d)), b)), m));
	assert(eq_(temp_7_0, temp_7_1)) by {
		lemma_eq_ref(m);
		lemma_mul_assoc(add_(a, a), d, b);
		cong_mod_(mul_(add_(a, a), mul_(d, b)), m, mul_(mul_(add_(a, a), d), b), m);
	}
	let temp_8_0 = (mul_((sub_(a, (mod_(c, m)))), (mul_(a, as_elem(1)))));
	let temp_8_1 = (mul_((sub_(a, (mod_((sub_(c, (mul_((mul_((mul_((mod_(b, m)), d)), (add_(c, b)))), m)))), m)))), (mul_(a, as_elem(1)))));
	assert(eq_(temp_8_0, temp_8_1)) by {
		lemma_mod_mul_vanish(c, mul_(mul_(mod_(b, m), d), add_(c, b)), m);
		cong_mul_(sub_(a, mod_(c, m)), mul_(a, as_elem(1)), sub_(a, mod_(sub_(c, mul_(mul_(mul_(mod_(b, m), d), add_(c, b)), m)), m)), mul_(a, as_elem(1)));
		cong_sub_(a, mod_(c, m), a, mod_(sub_(c, mul_(mul_(mul_(mod_(b, m), d), add_(c, b)), m)), m));
		lemma_eq_ref(mul_(a, as_elem(1)));
		lemma_eq_ref(a);
	}
	let temp_9_0 = (add_((mul_(a, b)), (mul_(c, b))));
	let temp_9_1 = (add_((mul_(b, a)), (mul_(c, b))));
	assert(eq_(temp_9_0, temp_9_1)) by {
		cong_add_(mul_(a, b), mul_(c, b), mul_(b, a), mul_(c, b));
		lemma_mul_comm(a, b);
		lemma_eq_ref(mul_(c, b));
	}
	let temp_10_0 = (mod_((mul_((add_(a, d)), (add_(d, b)))), m));
	let temp_10_1 = (mod_((mul_((add_(d, b)), (add_(a, d)))), m));
	assert(eq_(temp_10_0, temp_10_1)) by {
		lemma_mul_comm(add_(a, d), add_(d, b));
		cong_mod_(mul_(add_(a, d), add_(d, b)), m, mul_(add_(d, b), add_(a, d)), m);
		lemma_eq_ref(m);
	}
	let temp_11_0 = (sub_((sub_(a, b)), (mul_(a, a))));
	let temp_11_1 = (sub_((sub_(a, b)), (mul_(a, a))));
	assert(eq_(temp_11_0, temp_11_1)) by {
		lemma_eq_ref(temp_11_0);
	}
	let temp_12_0 = (add_((sub_(c, a)), d));
	let temp_12_1 = (add_(d, (sub_(c, a))));
	assert(eq_(temp_12_0, temp_12_1)) by {
		lemma_add_comm(sub_(c, a), d);
	}
	let temp_13_0 = (add_((mul_(c, b)), (mul_(a, b))));
	let temp_13_1 = (mul_((add_(c, a)), b));
	assert(eq_(temp_13_0, temp_13_1)) by {
		lemma_eq_sym(temp_13_1, temp_13_0);
		lemma_mul_dist(c, a, b);
	}
	let temp_14_0 = (mul_((mul_(c, d)), (mul_(d, a))));
	let temp_14_1 = (mul_((mul_(c, d)), (mul_(a, d))));
	assert(eq_(temp_14_0, temp_14_1)) by {
		cong_mul_(mul_(c, d), mul_(d, a), mul_(c, d), mul_(a, d));
		lemma_mul_comm(d, a);
		lemma_eq_ref(mul_(c, d));
	}
	let temp_15_0 = (mul_(d, (add_(a, c))));
	let temp_15_1 = (mul_(d, (add_(c, a))));
	assert(eq_(temp_15_0, temp_15_1)) by {
		cong_mul_(d, add_(a, c), d, add_(c, a));
		lemma_add_comm(a, c);
		lemma_eq_ref(d);
	}
	let temp_16_0 = (mul_((sub_(c, c)), (add_(b, b))));
	let temp_16_1 = (mul_((add_(b, b)), (sub_(c, c))));
	assert(eq_(temp_16_0, temp_16_1)) by {
		lemma_mul_comm(sub_(c, c), add_(b, b));
	}
	let temp_17_0 = (mod_((mul_((mod_((mul_(c, (mod_(d, m)))), m)), (mul_(a, d)))), m));
	let temp_17_1 = (mod_((mul_((mul_((mod_((mul_(c, (mod_(d, m)))), m)), a)), d)), m));
	assert(eq_(temp_17_0, temp_17_1)) by {
		lemma_mul_assoc(mod_(mul_(c, mod_(d, m)), m), a, d);
		cong_mod_(mul_(mod_(mul_(c, mod_(d, m)), m), mul_(a, d)), m, mul_(mul_(mod_(mul_(c, mod_(d, m)), m), a), d), m);
		lemma_eq_ref(m);
	}
	let temp_18_0 = (mul_((add_(c, b)), (mul_(c, a))));
	let temp_18_1 = (add_((mul_(c, (mul_(c, a)))), (mul_(b, (mul_(c, a))))));
	assert(eq_(temp_18_0, temp_18_1)) by {
		lemma_mul_dist(c, b, mul_(c, a));
	}
	let temp_19_0 = (mul_(b, (mul_(c, a))));
	let temp_19_1 = (mul_((mul_(b, c)), a));
	assert(eq_(temp_19_0, temp_19_1)) by {
		lemma_mul_assoc(b, c, a);
	}
	let temp_20_0 = (mul_((mul_((mod_(d, m)), b)), (mul_((mod_(c, m)), a))));
	let temp_20_1 = (mul_((mul_((mod_(d, m)), b)), (mul_((mod_((add_(c, (mul_((mul_((mul_(c, c)), (sub_(c, c)))), m)))), m)), a))));
	assert(eq_(temp_20_0, temp_20_1)) by {
		lemma_mod_mul_vanish(c, mul_(mul_(c, c), sub_(c, c)), m);
		cong_mul_(mul_(mod_(d, m), b), mul_(mod_(c, m), a), mul_(mod_(d, m), b), mul_(mod_(add_(c, mul_(mul_(mul_(c, c), sub_(c, c)), m)), m), a));
		lemma_eq_ref(a);
		lemma_eq_ref(mul_(mod_(d, m), b));
		cong_mul_(mod_(c, m), a, mod_(add_(c, mul_(mul_(mul_(c, c), sub_(c, c)), m)), m), a);
	}
	let temp_21_0 = (sub_((mul_(d, b)), (mul_(c, a))));
	let temp_21_1 = (sub_((mul_(b, d)), (mul_(c, a))));
	assert(eq_(temp_21_0, temp_21_1)) by {
		cong_sub_(mul_(d, b), mul_(c, a), mul_(b, d), mul_(c, a));
		lemma_mul_comm(d, b);
		lemma_eq_ref(mul_(c, a));
	}
	let temp_22_0 = (mul_((mul_(a, b)), (mul_(b, d))));
	let temp_22_1 = (mul_((mul_(b, d)), (mul_(a, b))));
	assert(eq_(temp_22_0, temp_22_1)) by {
		lemma_mul_comm(mul_(a, b), mul_(b, d));
	}
	let temp_23_0 = (mul_((mul_(c, d)), (mul_(b, a))));
	let temp_23_1 = (mul_(c, (mul_(d, (mul_(b, a))))));
	assert(eq_(temp_23_0, temp_23_1)) by {
		lemma_eq_sym(temp_23_1, temp_23_0);
		lemma_mul_assoc(c, d, mul_(b, a));
	}
	let temp_24_0 = (mul_((mul_(b, d)), (mod_((mul_(d, a)), m))));
	let temp_24_1 = (mul_((mul_(b, d)), (mod_((add_((mul_((mul_((mod_((mul_(d, a)), m)), (mul_(a, c)))), m)), (mul_(d, a)))), m))));
	assert(eq_(temp_24_0, temp_24_1)) by {
		lemma_mod_mul_vanish(mul_(d, a), mul_(mod_(mul_(d, a), m), mul_(a, c)), m);
		cong_mul_(mul_(b, d), mod_(mul_(d, a), m), mul_(b, d), mod_(add_(mul_(mul_(mod_(mul_(d, a), m), mul_(a, c)), m), mul_(d, a)), m));
		lemma_eq_ref(mul_(b, d));
	}
	let temp_25_0 = (sub_((sub_(a, d)), (mul_(b, b))));
	let temp_25_1 = (sub_((sub_(a, d)), (mul_(b, b))));
	assert(eq_(temp_25_0, temp_25_1)) by {
		lemma_eq_ref(temp_25_0);
	}
	let temp_26_0 = (mul_((sub_(c, a)), (mul_(c, c))));
	let temp_26_1 = (sub_((mul_(c, (mul_(c, c)))), (mul_(a, (mul_(c, c))))));
	assert(eq_(temp_26_0, temp_26_1)) by {
		lemma_mul_dist(mul_(c, c), c, a);
	}
	let temp_27_0 = (mul_((mul_(c, a)), (mul_(c, c))));
	let temp_27_1 = (mul_(c, (mul_(a, (mul_(c, c))))));
	assert(eq_(temp_27_0, temp_27_1)) by {
		lemma_eq_sym(temp_27_1, temp_27_0);
		lemma_mul_assoc(c, a, mul_(c, c));
	}
	let temp_28_0 = (mul_((mul_(b, b)), (mul_(c, a))));
	let temp_28_1 = (mul_((mul_(c, a)), (mul_(b, b))));
	assert(eq_(temp_28_0, temp_28_1)) by {
		lemma_mul_comm(mul_(b, b), mul_(c, a));
	}
	let temp_29_0 = (mul_((mul_(c, d)), (mul_(c, c))));
	let temp_29_1 = (mul_((mul_(c, c)), (mul_(c, d))));
	assert(eq_(temp_29_0, temp_29_1)) by {
		lemma_mul_comm(mul_(c, d), mul_(c, c));
	}
	let temp_30_0 = (mul_((mod_((mul_(d, b)), m)), (sub_(b, c))));
	let temp_30_1 = (mul_((mod_((mul_(b, d)), m)), (sub_(b, c))));
	assert(eq_(temp_30_0, temp_30_1)) by {
		lemma_mul_comm(d, b);
		cong_mul_(mod_(mul_(d, b), m), sub_(b, c), mod_(mul_(b, d), m), sub_(b, c));
		cong_mod_(mul_(d, b), m, mul_(b, d), m);
		lemma_eq_ref(sub_(b, c));
		lemma_eq_ref(m);
	}
	let temp_31_0 = (mul_((mul_(b, c)), (sub_(c, b))));
	let temp_31_1 = (mul_((sub_(c, b)), (mul_(b, c))));
	assert(eq_(temp_31_0, temp_31_1)) by {
		lemma_mul_comm(mul_(b, c), sub_(c, b));
	}
	let temp_32_0 = (add_((mul_(a, (mod_(a, m)))), a));
	let temp_32_1 = (add_((mul_((mod_(a, m)), a)), a));
	assert(eq_(temp_32_0, temp_32_1)) by {
		cong_add_(mul_(a, mod_(a, m)), a, mul_(mod_(a, m), a), a);
		lemma_mul_comm(a, mod_(a, m));
		lemma_eq_ref(a);
	}
	let temp_33_0 = (mod_((mul_((mul_((mod_(a, m)), c)), (mul_(d, c)))), m));
	let temp_33_1 = (mod_((mul_((mul_((mod_(a, m)), c)), (mul_(c, d)))), m));
	assert(eq_(temp_33_0, temp_33_1)) by {
		lemma_mul_comm(d, c);
		cong_mod_(mul_(mul_(mod_(a, m), c), mul_(d, c)), m, mul_(mul_(mod_(a, m), c), mul_(c, d)), m);
		lemma_eq_ref(mul_(mod_(a, m), c));
		cong_mul_(mul_(mod_(a, m), c), mul_(d, c), mul_(mod_(a, m), c), mul_(c, d));
		lemma_eq_ref(m);
	}
	let temp_34_0 = (mul_((mul_((mod_(a, m)), b)), (mul_(b, a))));
	let temp_34_1 = (mul_((mod_(a, m)), (mul_(b, (mul_(b, a))))));
	assert(eq_(temp_34_0, temp_34_1)) by {
		lemma_eq_sym(temp_34_1, temp_34_0);
		lemma_mul_assoc(mod_(a, m), b, mul_(b, a));
	}
	let temp_35_0 = (mul_((sub_(b, c)), (mul_(a, c))));
	let temp_35_1 = (sub_((mul_(b, (mul_(a, c)))), (mul_(c, (mul_(a, c))))));
	assert(eq_(temp_35_0, temp_35_1)) by {
		lemma_mul_dist(mul_(a, c), b, c);
	}
	let temp_36_0 = (mul_((mul_(as_elem(45), c)), (mod_((mul_(a, c)), m))));
	let temp_36_1 = (mul_((mul_(c, as_elem(45))), (mod_((mul_(a, c)), m))));
	assert(eq_(temp_36_0, temp_36_1)) by {
		lemma_mul_comm(as_elem(45), c);
		cong_mul_(mul_(as_elem(45), c), mod_(mul_(a, c), m), mul_(c, as_elem(45)), mod_(mul_(a, c), m));
		lemma_eq_ref(mod_(mul_(a, c), m));
	}
	let temp_37_0 = (mul_((sub_(a, c)), (mul_(d, c))));
	let temp_37_1 = (mul_((mul_(d, c)), (sub_(a, c))));
	assert(eq_(temp_37_0, temp_37_1)) by {
		lemma_mul_comm(sub_(a, c), mul_(d, c));
	}
	let temp_38_0 = (sub_((mul_(d, a)), (mul_(b, a))));
	let temp_38_1 = (sub_((mul_(d, a)), (mul_(a, b))));
	assert(eq_(temp_38_0, temp_38_1)) by {
		cong_sub_(mul_(d, a), mul_(b, a), mul_(d, a), mul_(a, b));
		lemma_mul_comm(b, a);
		lemma_eq_ref(mul_(d, a));
	}
	let temp_39_0 = (mul_((mod_((sub_(a, d)), m)), (add_(c, b))));
	let temp_39_1 = (mul_((add_(c, b)), (mod_((sub_(a, d)), m))));
	assert(eq_(temp_39_0, temp_39_1)) by {
		lemma_mul_comm(mod_(sub_(a, d), m), add_(c, b));
	}
	let temp_40_0 = (mul_((sub_(c, (mod_(d, m)))), (mul_(b, b))));
	let temp_40_1 = (mul_((sub_(c, (mod_((sub_(d, (mul_((mul_((sub_(a, c)), (mul_(c, b)))), m)))), m)))), (mul_(b, b))));
	assert(eq_(temp_40_0, temp_40_1)) by {
		lemma_mul_comm(b, b);
		lemma_mod_mul_vanish(d, mul_(sub_(a, c), mul_(c, b)), m);
		cong_mul_(sub_(c, mod_(d, m)), mul_(b, b), sub_(c, mod_(sub_(d, mul_(mul_(sub_(a, c), mul_(c, b)), m)), m)), mul_(b, b));
		cong_sub_(c, mod_(d, m), c, mod_(sub_(d, mul_(mul_(sub_(a, c), mul_(c, b)), m)), m));
		lemma_eq_ref(c);
	}
	let temp_41_0 = (add_((mod_((sub_(d, d)), m)), (mod_((mul_(c, d)), m))));
	let temp_41_1 = (add_((mod_((sub_(d, d)), m)), (mod_((mul_(d, c)), m))));
	assert(eq_(temp_41_0, temp_41_1)) by {
		lemma_mul_comm(c, d);
		cong_add_(mod_(sub_(d, d), m), mod_(mul_(c, d), m), mod_(sub_(d, d), m), mod_(mul_(d, c), m));
		cong_mod_(mul_(c, d), m, mul_(d, c), m);
		lemma_eq_ref(m);
		lemma_eq_ref(mod_(sub_(d, d), m));
	}
	let temp_42_0 = (mul_((mul_(d, as_elem(77))), (mul_(b, b))));
	let temp_42_1 = (mul_((mul_((mul_(d, as_elem(77))), b)), b));
	assert(eq_(temp_42_0, temp_42_1)) by {
		lemma_mul_assoc(mul_(d, as_elem(77)), b, b);
	}
	let temp_43_0 = (mul_((mul_((mod_(a, m)), a)), (mul_(a, a))));
	let temp_43_1 = (mul_((mul_(a, a)), (mul_((mod_(a, m)), a))));
	assert(eq_(temp_43_0, temp_43_1)) by {
		lemma_mul_comm(mul_(mod_(a, m), a), mul_(a, a));
	}
	let temp_44_0 = (mul_((mul_(d, a)), (mul_(b, c))));
	let temp_44_1 = (mul_(d, (mul_(a, (mul_(b, c))))));
	assert(eq_(temp_44_0, temp_44_1)) by {
		lemma_eq_sym(temp_44_1, temp_44_0);
		lemma_mul_assoc(d, a, mul_(b, c));
	}
	let temp_45_0 = (mul_((mul_(b, a)), (mul_(as_elem(75), d))));
	let temp_45_1 = (mul_(b, (mul_(a, (mul_(as_elem(75), d))))));
	assert(eq_(temp_45_0, temp_45_1)) by {
		lemma_mul_assoc(b, a, mul_(as_elem(75), d));
		lemma_eq_sym(temp_45_1, temp_45_0);
	}
	let temp_46_0 = (mul_((mul_(b, a)), (mul_(d, c))));
	let temp_46_1 = (mul_((mul_(b, a)), (mul_(c, d))));
	assert(eq_(temp_46_0, temp_46_1)) by {
		cong_mul_(mul_(b, a), mul_(d, c), mul_(b, a), mul_(c, d));
		lemma_mul_comm(d, c);
		lemma_eq_ref(mul_(b, a));
	}
	let temp_47_0 = (add_((mul_(c, a)), (add_((mod_(a, m)), b))));
	let temp_47_1 = (add_((mul_(c, a)), (add_((mod_((sub_(a, (mul_((mul_((mul_(b, c)), (mul_(a, b)))), m)))), m)), b))));
	assert(eq_(temp_47_0, temp_47_1)) by {
		lemma_mod_mul_vanish(a, mul_(mul_(b, c), mul_(a, b)), m);
		cong_add_(mul_(c, a), add_(mod_(a, m), b), mul_(c, a), add_(mod_(sub_(a, mul_(mul_(mul_(b, c), mul_(a, b)), m)), m), b));
		lemma_eq_ref(b);
		lemma_eq_ref(mul_(c, a));
		cong_add_(mod_(a, m), b, mod_(sub_(a, mul_(mul_(mul_(b, c), mul_(a, b)), m)), m), b);
	}
	let temp_48_0 = (mul_((add_(d, b)), (mul_(c, a))));
	let temp_48_1 = (mul_((add_(b, d)), (mul_(c, a))));
	assert(eq_(temp_48_0, temp_48_1)) by {
		lemma_add_comm(d, b);
		cong_mul_(add_(d, b), mul_(c, a), add_(b, d), mul_(c, a));
		lemma_eq_ref(mul_(c, a));
	}
	let temp_49_0 = (mod_((mul_((mod_((add_((mod_(b, m)), c)), m)), (sub_(b, c)))), m));
	let temp_49_1 = (mod_((mul_((mod_((add_(c, (mod_(b, m)))), m)), (sub_(b, c)))), m));
	assert(eq_(temp_49_0, temp_49_1)) by {
		lemma_add_comm(mod_(b, m), c);
		cong_mod_(mul_(mod_(add_(mod_(b, m), c), m), sub_(b, c)), m, mul_(mod_(add_(c, mod_(b, m)), m), sub_(b, c)), m);
		lemma_eq_ref(sub_(b, c));
		cong_mul_(mod_(add_(mod_(b, m), c), m), sub_(b, c), mod_(add_(c, mod_(b, m)), m), sub_(b, c));
		lemma_eq_ref(m);
		cong_mod_(add_(mod_(b, m), c), m, add_(c, mod_(b, m)), m);
	}
	let temp_50_0 = (mul_((mul_(a, b)), (mul_(c, c))));
	let temp_50_1 = (mul_((mul_(c, c)), (mul_(a, b))));
	assert(eq_(temp_50_0, temp_50_1)) by {
		lemma_mul_comm(mul_(a, b), mul_(c, c));
	}
	let temp_51_0 = (mul_((mul_(b, b)), (mul_(c, (mod_(d, m))))));
	let temp_51_1 = (mul_((mul_(b, b)), (mul_(c, (mod_((add_(d, (mul_((mul_((mul_(a, a)), (add_(c, a)))), m)))), m))))));
	assert(eq_(temp_51_0, temp_51_1)) by {
		lemma_mul_comm(b, b);
		lemma_mod_mul_vanish(d, mul_(mul_(a, a), add_(c, a)), m);
		cong_mul_(mul_(b, b), mul_(c, mod_(d, m)), mul_(b, b), mul_(c, mod_(add_(d, mul_(mul_(mul_(a, a), add_(c, a)), m)), m)));
		lemma_eq_ref(c);
		cong_mul_(c, mod_(d, m), c, mod_(add_(d, mul_(mul_(mul_(a, a), add_(c, a)), m)), m));
	}
	let temp_52_0 = (sub_((sub_(b, a)), (mul_(b, c))));
	let temp_52_1 = (sub_((sub_(b, a)), (mul_(c, b))));
	assert(eq_(temp_52_0, temp_52_1)) by {
		cong_sub_(sub_(b, a), mul_(b, c), sub_(b, a), mul_(c, b));
		lemma_mul_comm(b, c);
		lemma_eq_ref(sub_(b, a));
	}
	let temp_53_0 = (mul_((mul_(a, (mod_(b, m)))), (mod_((mul_(d, d)), m))));
	let temp_53_1 = (mul_((mul_(a, (mod_(b, m)))), (mod_((sub_((mul_(d, d)), (mul_((mul_((mul_(a, a)), (mul_(b, c)))), m)))), m))));
	assert(eq_(temp_53_0, temp_53_1)) by {
		lemma_mod_mul_vanish(mul_(d, d), mul_(mul_(a, a), mul_(b, c)), m);
		cong_mul_(mul_(a, mod_(b, m)), mod_(mul_(d, d), m), mul_(a, mod_(b, m)), mod_(sub_(mul_(d, d), mul_(mul_(mul_(a, a), mul_(b, c)), m)), m));
		lemma_eq_ref(mul_(a, mod_(b, m)));
	}
	let temp_54_0 = (mul_((add_(c, d)), (mul_((mod_(b, m)), a))));
	let temp_54_1 = (mul_((add_(d, c)), (mul_((mod_(b, m)), a))));
	assert(eq_(temp_54_0, temp_54_1)) by {
		lemma_add_comm(c, d);
		cong_mul_(add_(c, d), mul_(mod_(b, m), a), add_(d, c), mul_(mod_(b, m), a));
		lemma_eq_ref(mul_(mod_(b, m), a));
	}
	let temp_55_0 = (sub_((mod_((sub_(b, c)), m)), (mul_(b, a))));
	let temp_55_1 = (sub_((mod_((sub_((mod_(b, m)), c)), m)), (mul_(b, a))));
	assert(eq_(temp_55_0, temp_55_1)) by {
		cong_sub_(mod_(sub_(b, c), m), mul_(b, a), mod_(sub_(mod_(b, m), c), m), mul_(b, a));
		lemma_mod_sub_noop(b, c, m);
		lemma_eq_ref(mul_(b, a));
	}
	let temp_56_0 = (mul_((mul_(c, d)), (mul_(a, b))));
	let temp_56_1 = (mul_((mul_((mul_(c, d)), a)), b));
	assert(eq_(temp_56_0, temp_56_1)) by {
		lemma_mul_assoc(mul_(c, d), a, b);
	}
	let temp_57_0 = (mul_((mod_((mul_(d, d)), m)), (mul_(c, a))));
	let temp_57_1 = (mul_((mod_((add_((mul_(d, d)), (mul_((mul_((sub_(b, a)), (mul_(c, b)))), m)))), m)), (mul_(c, a))));
	assert(eq_(temp_57_0, temp_57_1)) by {
		lemma_mod_mul_vanish(mul_(d, d), mul_(sub_(b, a), mul_(c, b)), m);
		cong_mul_(mod_(mul_(d, d), m), mul_(c, a), mod_(add_(mul_(d, d), mul_(mul_(sub_(b, a), mul_(c, b)), m)), m), mul_(c, a));
		lemma_eq_ref(mul_(c, a));
	}
	let temp_58_0 = (mul_((mul_(a, c)), (mod_((mul_(c, (mod_(c, m)))), m))));
	let temp_58_1 = (mul_((mul_(a, c)), (mod_((mod_((mul_(c, c)), m)), m))));
	assert(eq_(temp_58_0, temp_58_1)) by {
		lemma_mod_mul_noop(c, c, m);
		cong_mul_(mul_(a, c), mod_(mul_(c, mod_(c, m)), m), mul_(a, c), mod_(mod_(mul_(c, c), m), m));
		lemma_eq_sym(mod_(mod_(mul_(c, c), m), m), mod_(mul_(c, mod_(c, m)), m));
		lemma_eq_ref(mul_(a, c));
	}
	let temp_59_0 = (mul_(b, (mul_((mod_(c, m)), c))));
	let temp_59_1 = (mul_(b, (mul_((mod_((add_((mul_((mul_((mul_(d, c)), (mul_(c, (mod_(c, m)))))), m)), c)), m)), c))));
	assert(eq_(temp_59_0, temp_59_1)) by {
		lemma_mod_mul_vanish(c, mul_(mul_(d, c), mul_(c, mod_(c, m))), m);
		cong_mul_(b, mul_(mod_(c, m), c), b, mul_(mod_(add_(mul_(mul_(mul_(d, c), mul_(c, mod_(c, m))), m), c), m), c));
		lemma_eq_ref(b);
		lemma_eq_ref(c);
		cong_mul_(mod_(c, m), c, mod_(add_(mul_(mul_(mul_(d, c), mul_(c, mod_(c, m))), m), c), m), c);
	}
	let temp_60_0 = (mul_((mul_(d, d)), (mul_(d, b))));
	let temp_60_1 = (mul_((mul_((mul_(d, d)), d)), b));
	assert(eq_(temp_60_0, temp_60_1)) by {
		lemma_mul_assoc(mul_(d, d), d, b);
	}
	let temp_61_0 = (mul_((mul_(b, b)), (mod_((mul_(c, (mod_(d, m)))), m))));
	let temp_61_1 = (mul_((mul_(b, b)), (mod_((sub_((mul_(c, (mod_(d, m)))), (mul_((mul_((mod_((add_(a, c)), m)), (mul_(a, c)))), m)))), m))));
	assert(eq_(temp_61_0, temp_61_1)) by {
		lemma_mul_comm(b, b);
		lemma_mod_mul_vanish(mul_(c, mod_(d, m)), mul_(mod_(add_(a, c), m), mul_(a, c)), m);
		cong_mul_(mul_(b, b), mod_(mul_(c, mod_(d, m)), m), mul_(b, b), mod_(sub_(mul_(c, mod_(d, m)), mul_(mul_(mod_(add_(a, c), m), mul_(a, c)), m)), m));
	}
	let temp_62_0 = (sub_((mul_(d, d)), (mod_((mul_(a, c)), m))));
	let temp_62_1 = (sub_((mul_(d, d)), (mod_((add_((mul_(a, c)), (mul_((mul_((add_(b, d)), (mul_(d, b)))), m)))), m))));
	assert(eq_(temp_62_0, temp_62_1)) by {
		lemma_mul_comm(d, d);
		lemma_mod_mul_vanish(mul_(a, c), mul_(add_(b, d), mul_(d, b)), m);
		cong_sub_(mul_(d, d), mod_(mul_(a, c), m), mul_(d, d), mod_(add_(mul_(a, c), mul_(mul_(add_(b, d), mul_(d, b)), m)), m));
	}
	let temp_63_0 = (mul_((mul_(b, (mod_(b, m)))), (mul_(b, c))));
	let temp_63_1 = (mul_((mul_((mod_(b, m)), b)), (mul_(b, c))));
	assert(eq_(temp_63_0, temp_63_1)) by {
		cong_mul_(mul_(b, mod_(b, m)), mul_(b, c), mul_(mod_(b, m), b), mul_(b, c));
		lemma_mul_comm(b, mod_(b, m));
		lemma_eq_ref(mul_(b, c));
	}
	let temp_64_0 = (mul_((sub_(c, d)), (mul_(c, a))));
	let temp_64_1 = (mul_((mul_(c, a)), (sub_(c, d))));
	assert(eq_(temp_64_0, temp_64_1)) by {
		lemma_mul_comm(sub_(c, d), mul_(c, a));
	}
	let temp_65_0 = (mul_((mul_(b, a)), (mul_(c, d))));
	let temp_65_1 = (mul_((mul_(a, b)), (mul_(c, d))));
	assert(eq_(temp_65_0, temp_65_1)) by {
		cong_mul_(mul_(b, a), mul_(c, d), mul_(a, b), mul_(c, d));
		lemma_mul_comm(b, a);
		lemma_eq_ref(mul_(c, d));
	}
	let temp_66_0 = (mod_((mul_((mul_(b, d)), (add_(c, d)))), m));
	let temp_66_1 = (mod_((add_((mul_((mul_(b, d)), c)), (mul_((mul_(b, d)), d)))), m));
	assert(eq_(temp_66_0, temp_66_1)) by {
		lemma_mul_dist(mul_(b, d), c, d);
		cong_mod_(mul_(mul_(b, d), add_(c, d)), m, add_(mul_(mul_(b, d), c), mul_(mul_(b, d), d)), m);
		lemma_eq_ref(m);
	}
	let temp_67_0 = (mul_((mul_((mod_(c, m)), b)), (sub_(c, a))));
	let temp_67_1 = (mul_((mul_(b, (mod_(c, m)))), (sub_(c, a))));
	assert(eq_(temp_67_0, temp_67_1)) by {
		lemma_mul_comm(mod_(c, m), b);
		cong_mul_(mul_(mod_(c, m), b), sub_(c, a), mul_(b, mod_(c, m)), sub_(c, a));
		lemma_eq_ref(sub_(c, a));
	}
	let temp_68_0 = (sub_((sub_(d, d)), (mul_((mod_(b, m)), c))));
	let temp_68_1 = (sub_((sub_(d, d)), (mul_(c, (mod_(b, m))))));
	assert(eq_(temp_68_0, temp_68_1)) by {
		lemma_mul_comm(mod_(b, m), c);
		cong_sub_(sub_(d, d), mul_(mod_(b, m), c), sub_(d, d), mul_(c, mod_(b, m)));
		lemma_eq_ref(sub_(d, d));
	}
	let temp_69_0 = (mul_((mul_(b, (mod_(d, m)))), (mul_(a, a))));
	let temp_69_1 = (mul_((mul_(b, (mod_((add_(d, (mul_((mul_(b, (mul_(b, a)))), m)))), m)))), (mul_(a, a))));
	assert(eq_(temp_69_0, temp_69_1)) by {
		lemma_mul_comm(a, a);
		lemma_mod_mul_vanish(d, mul_(b, mul_(b, a)), m);
		cong_mul_(mul_(b, mod_(d, m)), mul_(a, a), mul_(b, mod_(add_(d, mul_(mul_(b, mul_(b, a)), m)), m)), mul_(a, a));
		lemma_eq_ref(b);
		cong_mul_(b, mod_(d, m), b, mod_(add_(d, mul_(mul_(b, mul_(b, a)), m)), m));
	}
	let temp_70_0 = (mul_((mul_(c, b)), (mul_(d, a))));
	let temp_70_1 = (mul_(c, (mul_(b, (mul_(d, a))))));
	assert(eq_(temp_70_0, temp_70_1)) by {
		lemma_eq_sym(temp_70_1, temp_70_0);
		lemma_mul_assoc(c, b, mul_(d, a));
	}
	let temp_71_0 = (mul_((mul_(a, (mod_(b, m)))), c));
	let temp_71_1 = (mul_((mul_(a, (mod_((sub_(b, (mul_((mul_((add_(b, c)), (add_(d, c)))), m)))), m)))), c));
	assert(eq_(temp_71_0, temp_71_1)) by {
		lemma_mod_mul_vanish(b, mul_(add_(b, c), add_(d, c)), m);
		cong_mul_(mul_(a, mod_(b, m)), c, mul_(a, mod_(sub_(b, mul_(mul_(add_(b, c), add_(d, c)), m)), m)), c);
		lemma_eq_ref(a);
		cong_mul_(a, mod_(b, m), a, mod_(sub_(b, mul_(mul_(add_(b, c), add_(d, c)), m)), m));
		lemma_eq_ref(c);
	}
	let temp_72_0 = (sub_((add_(b, b)), d));
	let temp_72_1 = (sub_((add_(b, b)), d));
	assert(eq_(temp_72_0, temp_72_1)) by {
		lemma_eq_ref(temp_72_0);
	}
	let temp_73_0 = (mod_((sub_((mul_(a, a)), (mul_(b, b)))), m));
	let temp_73_1 = (mod_((sub_((sub_((mul_(a, a)), (mul_(b, b)))), (mul_((mul_((mul_(as_elem(30), b)), (mul_(b, c)))), m)))), m));
	assert(eq_(temp_73_0, temp_73_1)) by {
		lemma_mod_mul_vanish(sub_(mul_(a, a), mul_(b, b)), mul_(mul_(as_elem(30), b), mul_(b, c)), m);
	}
	let temp_74_0 = (mul_((mul_(a, c)), (mod_((mul_(c, a)), m))));
	let temp_74_1 = (mul_((mul_(a, c)), (mod_((mul_(a, c)), m))));
	assert(eq_(temp_74_0, temp_74_1)) by {
		cong_mul_(mul_(a, c), mod_(mul_(c, a), m), mul_(a, c), mod_(mul_(a, c), m));
		lemma_mul_comm(c, a);
		cong_mod_(mul_(c, a), m, mul_(a, c), m);
		lemma_eq_ref(mul_(a, c));
		lemma_eq_ref(m);
	}
	let temp_75_0 = (mul_((sub_(d, a)), (mod_((mul_(c, b)), m))));
	let temp_75_1 = (mul_((sub_(d, a)), (mod_((sub_((mul_(c, b)), (mul_((mul_((add_(as_elem(89), d)), (mul_(a, (mod_(c, m)))))), m)))), m))));
	assert(eq_(temp_75_0, temp_75_1)) by {
		cong_mul_(sub_(d, a), mod_(mul_(c, b), m), sub_(d, a), mod_(sub_(mul_(c, b), mul_(mul_(add_(as_elem(89), d), mul_(a, mod_(c, m))), m)), m));
		lemma_mod_mul_vanish(mul_(c, b), mul_(add_(as_elem(89), d), mul_(a, mod_(c, m))), m);
		lemma_eq_ref(sub_(d, a));
	}
	let temp_76_0 = (mul_((mul_(a, a)), (mul_(a, (mod_(c, m))))));
	let temp_76_1 = (mul_((mul_(a, a)), (mul_((mod_(c, m)), a))));
	assert(eq_(temp_76_0, temp_76_1)) by {
		cong_mul_(mul_(a, a), mul_(a, mod_(c, m)), mul_(a, a), mul_(mod_(c, m), a));
		lemma_mul_comm(a, a);
		lemma_mul_comm(a, mod_(c, m));
	}
	let temp_77_0 = (mod_((mul_((mod_((mul_(a, d)), m)), (mul_(as_elem(26), b)))), m));
	let temp_77_1 = (mod_((mul_((mul_((mod_((mul_(a, d)), m)), as_elem(26))), b)), m));
	assert(eq_(temp_77_0, temp_77_1)) by {
		lemma_eq_ref(m);
		lemma_mul_assoc(mod_(mul_(a, d), m), as_elem(26), b);
		cong_mod_(mul_(mod_(mul_(a, d), m), mul_(as_elem(26), b)), m, mul_(mul_(mod_(mul_(a, d), m), as_elem(26)), b), m);
	}
	let temp_78_0 = (mul_((mul_(d, (mod_(c, m)))), (mul_(b, b))));
	let temp_78_1 = (mul_((mul_(d, (mod_((add_((mul_((mod_((mul_((mod_((mul_(a, b)), m)), (mul_(c, a)))), m)), m)), c)), m)))), (mul_(b, b))));
	assert(eq_(temp_78_0, temp_78_1)) by {
		lemma_mul_comm(b, b);
		lemma_mod_mul_vanish(c, mod_(mul_(mod_(mul_(a, b), m), mul_(c, a)), m), m);
		cong_mul_(mul_(d, mod_(c, m)), mul_(b, b), mul_(d, mod_(add_(mul_(mod_(mul_(mod_(mul_(a, b), m), mul_(c, a)), m), m), c), m)), mul_(b, b));
		lemma_eq_ref(d);
		cong_mul_(d, mod_(c, m), d, mod_(add_(mul_(mod_(mul_(mod_(mul_(a, b), m), mul_(c, a)), m), m), c), m));
	}
	let temp_79_0 = (mul_((add_(c, c)), (add_(d, b))));
	let temp_79_1 = (add_((mul_((add_(c, c)), d)), (mul_((add_(c, c)), b))));
	assert(eq_(temp_79_0, temp_79_1)) by {
		lemma_mul_dist(add_(c, c), d, b);
	}
	let temp_80_0 = (mul_((mul_(c, d)), (mul_(as_elem(38), a))));
	let temp_80_1 = (mul_(c, (mul_(d, (mul_(as_elem(38), a))))));
	assert(eq_(temp_80_0, temp_80_1)) by {
		lemma_mul_assoc(c, d, mul_(as_elem(38), a));
		lemma_eq_sym(temp_80_1, temp_80_0);
	}
	let temp_81_0 = (mod_((mul_(d, (mul_(a, b)))), m));
	let temp_81_1 = (mod_((sub_((mul_(d, (mul_(a, b)))), (mul_((mul_((mul_(a, c)), (mul_(d, b)))), m)))), m));
	assert(eq_(temp_81_0, temp_81_1)) by {
		lemma_mod_mul_vanish(mul_(d, mul_(a, b)), mul_(mul_(a, c), mul_(d, b)), m);
	}
	let temp_82_0 = (mul_((mul_(as_elem(23), b)), (mul_(a, d))));
	let temp_82_1 = (mul_((mul_((mul_(as_elem(23), b)), a)), d));
	assert(eq_(temp_82_0, temp_82_1)) by {
		lemma_mul_assoc(mul_(as_elem(23), b), a, d);
	}
	let temp_83_0 = (mul_((mul_(d, c)), (mul_(a, d))));
	let temp_83_1 = (mul_(d, (mul_(c, (mul_(a, d))))));
	assert(eq_(temp_83_0, temp_83_1)) by {
		lemma_eq_sym(temp_83_1, temp_83_0);
		lemma_mul_assoc(d, c, mul_(a, d));
	}
	let temp_84_0 = (mul_((mul_(a, d)), (sub_(c, a))));
	let temp_84_1 = (mul_(a, (mul_(d, (sub_(c, a))))));
	assert(eq_(temp_84_0, temp_84_1)) by {
		lemma_eq_sym(temp_84_1, temp_84_0);
		lemma_mul_assoc(a, d, sub_(c, a));
	}
	let temp_85_0 = (mul_((mul_(d, d)), (mod_((mul_((mod_(b, m)), b)), m))));
	let temp_85_1 = (mul_((mod_((mul_((mod_(b, m)), b)), m)), (mul_(d, d))));
	assert(eq_(temp_85_0, temp_85_1)) by {
		lemma_mul_comm(mul_(d, d), mod_(mul_(mod_(b, m), b), m));
	}
	let temp_86_0 = (mul_((add_(d, d)), (mul_(a, b))));
	let temp_86_1 = (mul_((add_(d, d)), (mul_(a, b))));
	assert(eq_(temp_86_0, temp_86_1)) by {
		lemma_eq_ref(temp_86_0);
	}
	let temp_87_0 = (mul_((sub_(d, c)), (mul_(b, b))));
	let temp_87_1 = (mul_((mul_((sub_(d, c)), b)), b));
	assert(eq_(temp_87_0, temp_87_1)) by {
		lemma_mul_assoc(sub_(d, c), b, b);
	}
	let temp_88_0 = (mul_((mul_(d, a)), (mod_((mul_(c, a)), m))));
	let temp_88_1 = (mul_((mod_((mul_(c, a)), m)), (mul_(d, a))));
	assert(eq_(temp_88_0, temp_88_1)) by {
		lemma_mul_comm(mul_(d, a), mod_(mul_(c, a), m));
	}
	let temp_89_0 = (mul_((mul_(a, a)), (mul_(a, a))));
	let temp_89_1 = (mul_(a, (mul_(a, (mul_(a, a))))));
	assert(eq_(temp_89_0, temp_89_1)) by {
		lemma_eq_sym(temp_89_1, temp_89_0);
		lemma_mul_assoc(a, a, mul_(a, a));
	}
	let temp_90_0 = (sub_((mul_(a, c)), (mul_(c, d))));
	let temp_90_1 = (sub_((mul_(c, a)), (mul_(c, d))));
	assert(eq_(temp_90_0, temp_90_1)) by {
		cong_sub_(mul_(a, c), mul_(c, d), mul_(c, a), mul_(c, d));
		lemma_mul_comm(a, c);
		lemma_eq_ref(mul_(c, d));
	}
	let temp_91_0 = (mul_((mul_(a, b)), (mod_((add_(c, d)), m))));
	let temp_91_1 = (mul_((mul_(a, b)), (mod_((add_((mod_(c, m)), d)), m))));
	assert(eq_(temp_91_0, temp_91_1)) by {
		lemma_mod_add_noop(c, d, m);
		cong_mul_(mul_(a, b), mod_(add_(c, d), m), mul_(a, b), mod_(add_(mod_(c, m), d), m));
		lemma_eq_ref(mul_(a, b));
	}
	let temp_92_0 = (mul_((mul_(b, d)), (mod_((mul_((mod_(a, m)), b)), m))));
	let temp_92_1 = (mul_((mul_(b, d)), (mod_((mul_((mod_((sub_(a, (mul_((mul_((mul_(b, d)), (mul_((mod_(a, m)), a)))), m)))), m)), b)), m))));
	assert(eq_(temp_92_0, temp_92_1)) by {
		lemma_mod_mul_vanish(a, mul_(mul_(b, d), mul_(mod_(a, m), a)), m);
		cong_mul_(mul_(b, d), mod_(mul_(mod_(a, m), b), m), mul_(b, d), mod_(mul_(mod_(sub_(a, mul_(mul_(mul_(b, d), mul_(mod_(a, m), a)), m)), m), b), m));
		lemma_eq_ref(mul_(b, d));
		cong_mod_(mul_(mod_(a, m), b), m, mul_(mod_(sub_(a, mul_(mul_(mul_(b, d), mul_(mod_(a, m), a)), m)), m), b), m);
		lemma_eq_ref(b);
		cong_mul_(mod_(a, m), b, mod_(sub_(a, mul_(mul_(mul_(b, d), mul_(mod_(a, m), a)), m)), m), b);
		lemma_eq_ref(m);
	}
	let temp_93_0 = (mul_((mul_(b, a)), (mul_(b, b))));
	let temp_93_1 = (mul_((mul_(b, b)), (mul_(b, a))));
	assert(eq_(temp_93_0, temp_93_1)) by {
		lemma_mul_comm(mul_(b, a), mul_(b, b));
	}
	let temp_94_0 = (mul_((mul_(a, c)), (sub_(d, c))));
	let temp_94_1 = (mul_(a, (mul_(c, (sub_(d, c))))));
	assert(eq_(temp_94_0, temp_94_1)) by {
		lemma_eq_sym(temp_94_1, temp_94_0);
		lemma_mul_assoc(a, c, sub_(d, c));
	}
	let temp_95_0 = (mul_((mul_(a, c)), (mul_(b, b))));
	let temp_95_1 = (mul_((mul_(a, c)), (mul_(b, b))));
	assert(eq_(temp_95_0, temp_95_1)) by {
		lemma_eq_ref(temp_95_0);
	}
	let temp_96_0 = (mul_((mul_(a, d)), (mul_(b, c))));
	let temp_96_1 = (mul_((mul_(d, a)), (mul_(b, c))));
	assert(eq_(temp_96_0, temp_96_1)) by {
		cong_mul_(mul_(a, d), mul_(b, c), mul_(d, a), mul_(b, c));
		lemma_mul_comm(a, d);
		lemma_eq_ref(mul_(b, c));
	}
	let temp_97_0 = (mul_((mul_(d, d)), (mul_((mod_(a, m)), c))));
	let temp_97_1 = (mul_((mul_(d, d)), (mul_((mod_((sub_(a, (mul_((mul_((add_(c, b)), (mul_(b, a)))), m)))), m)), c))));
	assert(eq_(temp_97_0, temp_97_1)) by {
		lemma_mul_comm(d, d);
		lemma_mod_mul_vanish(a, mul_(add_(c, b), mul_(b, a)), m);
		cong_mul_(mul_(d, d), mul_(mod_(a, m), c), mul_(d, d), mul_(mod_(sub_(a, mul_(mul_(add_(c, b), mul_(b, a)), m)), m), c));
		lemma_eq_ref(c);
		cong_mul_(mod_(a, m), c, mod_(sub_(a, mul_(mul_(add_(c, b), mul_(b, a)), m)), m), c);
	}
	let temp_98_0 = (mod_((mul_((mul_(b, a)), (add_(b, b)))), m));
	let temp_98_1 = (mod_((mul_((add_(b, b)), (mul_(b, a)))), m));
	assert(eq_(temp_98_0, temp_98_1)) by {
		cong_mod_(mul_(mul_(b, a), add_(b, b)), m, mul_(add_(b, b), mul_(b, a)), m);
		lemma_mul_comm(mul_(b, a), add_(b, b));
		lemma_eq_ref(m);
	}
	let temp_99_0 = (sub_((mul_((mod_(b, m)), c)), (mul_(c, b))));
	let temp_99_1 = (sub_((mul_((mod_(b, m)), c)), (mul_(b, c))));
	assert(eq_(temp_99_0, temp_99_1)) by {
		cong_sub_(mul_(mod_(b, m), c), mul_(c, b), mul_(mod_(b, m), c), mul_(b, c));
		lemma_mul_comm(c, b);
		lemma_eq_ref(mul_(mod_(b, m), c));
	}
	let temp_100_0 = (mul_((mul_(a, b)), (add_(c, a))));
	let temp_100_1 = (mul_(a, (mul_(b, (add_(c, a))))));
	assert(eq_(temp_100_0, temp_100_1)) by {
		lemma_eq_sym(temp_100_1, temp_100_0);
		lemma_mul_assoc(a, b, add_(c, a));
	}
	let temp_101_0 = (mod_((mul_((mul_(b, c)), (mul_(c, a)))), m));
	let temp_101_1 = (mod_((mul_(b, (mul_(c, (mul_(c, a)))))), m));
	assert(eq_(temp_101_0, temp_101_1)) by {
		lemma_mul_assoc(b, c, mul_(c, a));
		cong_mod_(mul_(mul_(b, c), mul_(c, a)), m, mul_(b, mul_(c, mul_(c, a))), m);
		lemma_eq_sym(mul_(b, mul_(c, mul_(c, a))), mul_(mul_(b, c), mul_(c, a)));
		lemma_eq_ref(m);
	}
	let temp_102_0 = (mul_((mod_((mul_(a, c)), m)), (mul_(d, d))));
	let temp_102_1 = (mul_((mod_((add_((mul_(a, c)), (mul_((mul_((mul_((mod_(b, m)), c)), (mul_(a, c)))), m)))), m)), (mul_(d, d))));
	assert(eq_(temp_102_0, temp_102_1)) by {
		lemma_mul_comm(d, d);
		lemma_mod_mul_vanish(mul_(a, c), mul_(mul_(mod_(b, m), c), mul_(a, c)), m);
		cong_mul_(mod_(mul_(a, c), m), mul_(d, d), mod_(add_(mul_(a, c), mul_(mul_(mul_(mod_(b, m), c), mul_(a, c)), m)), m), mul_(d, d));
	}
	let temp_103_0 = (mod_((mul_((mul_(c, (mod_(d, m)))), (mul_(b, a)))), m));
	let temp_103_1 = (mod_((mul_((mul_((mul_(c, (mod_(d, m)))), b)), a)), m));
	assert(eq_(temp_103_0, temp_103_1)) by {
		lemma_eq_ref(m);
		lemma_mul_assoc(mul_(c, mod_(d, m)), b, a);
		cong_mod_(mul_(mul_(c, mod_(d, m)), mul_(b, a)), m, mul_(mul_(mul_(c, mod_(d, m)), b), a), m);
	}
	let temp_104_0 = (mul_((mul_(a, (mod_(c, m)))), (sub_(d, d))));
	let temp_104_1 = (mul_(a, (mul_((mod_(c, m)), (sub_(d, d))))));
	assert(eq_(temp_104_0, temp_104_1)) by {
		lemma_mul_assoc(a, mod_(c, m), sub_(d, d));
		lemma_eq_sym(temp_104_1, temp_104_0);
	}
	let temp_105_0 = (add_((mul_(as_elem(16), a)), (mul_(d, d))));
	let temp_105_1 = (add_((mul_(as_elem(16), a)), (mul_(d, d))));
	assert(eq_(temp_105_0, temp_105_1)) by {
		lemma_eq_ref(temp_105_0);
	}
	let temp_106_0 = (mul_((mul_(a, (mod_(b, m)))), (sub_(a, as_elem(35)))));
	let temp_106_1 = (mul_(a, (mul_((mod_(b, m)), (sub_(a, as_elem(35)))))));
	assert(eq_(temp_106_0, temp_106_1)) by {
		lemma_mul_assoc(a, mod_(b, m), sub_(a, as_elem(35)));
		lemma_eq_sym(temp_106_1, temp_106_0);
	}
	let temp_107_0 = (mul_((mul_(d, b)), (mul_(c, a))));
	let temp_107_1 = (mul_((mul_(b, d)), (mul_(c, a))));
	assert(eq_(temp_107_0, temp_107_1)) by {
		cong_mul_(mul_(d, b), mul_(c, a), mul_(b, d), mul_(c, a));
		lemma_mul_comm(d, b);
		lemma_eq_ref(mul_(c, a));
	}
	let temp_108_0 = (sub_((sub_(d, b)), (mul_((mod_(a, m)), b))));
	let temp_108_1 = (sub_((sub_(d, b)), (mul_(b, (mod_(a, m))))));
	assert(eq_(temp_108_0, temp_108_1)) by {
		lemma_mul_comm(mod_(a, m), b);
		cong_sub_(sub_(d, b), mul_(mod_(a, m), b), sub_(d, b), mul_(b, mod_(a, m)));
		lemma_eq_ref(sub_(d, b));
	}
	let temp_109_0 = (mul_((mul_(b, b)), (mod_((mul_((mod_(a, m)), c)), m))));
	let temp_109_1 = (mul_((mul_(b, b)), (mod_((sub_((mul_((mod_(a, m)), c)), (mul_((mul_((mul_(c, as_elem(18))), (mul_(d, c)))), m)))), m))));
	assert(eq_(temp_109_0, temp_109_1)) by {
		lemma_mul_comm(b, b);
		cong_mul_(mul_(b, b), mod_(mul_(mod_(a, m), c), m), mul_(b, b), mod_(sub_(mul_(mod_(a, m), c), mul_(mul_(mul_(c, as_elem(18)), mul_(d, c)), m)), m));
		lemma_mod_mul_vanish(mul_(mod_(a, m), c), mul_(mul_(c, as_elem(18)), mul_(d, c)), m);
	}

}

} // verus!