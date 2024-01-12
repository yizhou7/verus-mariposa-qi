use builtin_macros::*;
// use builtin::*;
mod nl_basics;
use crate::nl_basics::*;
verus! {

pub proof fn free_0(a: Elem, b: Elem, c: Elem, d: Elem, m: Elem)
{
	let temp_0_0 = (mul_((mul_(d, c)), (sub_(d, b))));
	let temp_0_1 = (mul_((mul_(c, d)), (sub_(d, b))));
	assert(eq_(temp_0_0, temp_0_1)) by {
		cong_mul_(mul_(d, c), sub_(d, b), mul_(c, d), sub_(d, b));
		lemma_mul_comm(d, c);
		lemma_eq_ref(sub_(d, b));
	}
	let temp_1_0 = (mul_((mul_((mod_(d, m)), b)), (mod_((mul_(d, d)), m))));
	let temp_1_1 = (mul_((mul_(b, (mod_(d, m)))), (mod_((mul_(d, d)), m))));
	assert(eq_(temp_1_0, temp_1_1)) by {
		lemma_mul_comm(mod_(d, m), b);
		cong_mul_(mul_(mod_(d, m), b), mod_(mul_(d, d), m), mul_(b, mod_(d, m)), mod_(mul_(d, d), m));
		lemma_eq_ref(mod_(mul_(d, d), m));
	}
	let temp_2_0 = (sub_((mul_(b, (mod_(b, m)))), (mul_(d, a))));
	let temp_2_1 = (sub_((mul_((mod_(b, m)), b)), (mul_(d, a))));
	assert(eq_(temp_2_0, temp_2_1)) by {
		lemma_mul_comm(b, mod_(b, m));
		cong_sub_(mul_(b, mod_(b, m)), mul_(d, a), mul_(mod_(b, m), b), mul_(d, a));
		lemma_eq_ref(mul_(d, a));
	}
	let temp_3_0 = (mul_((mul_((mod_(a, m)), a)), (add_(c, a))));
	let temp_3_1 = (mul_((mod_(a, m)), (mul_(a, (add_(c, a))))));
	assert(eq_(temp_3_0, temp_3_1)) by {
		lemma_eq_sym(temp_3_1, temp_3_0);
		lemma_mul_assoc(mod_(a, m), a, add_(c, a));
	}
	let temp_4_0 = (mul_((mul_(d, d)), (mul_(b, b))));
	let temp_4_1 = (mul_(d, (mul_(d, (mul_(b, b))))));
	assert(eq_(temp_4_0, temp_4_1)) by {
		lemma_eq_sym(temp_4_1, temp_4_0);
		lemma_mul_assoc(d, d, mul_(b, b));
	}
	let temp_5_0 = (mul_((mul_(a, (mod_(a, m)))), (mod_((mul_(b, d)), m))));
	let temp_5_1 = (mul_((mod_((mul_(b, d)), m)), (mul_(a, (mod_(a, m))))));
	assert(eq_(temp_5_0, temp_5_1)) by {
		lemma_mul_comm(mul_(a, mod_(a, m)), mod_(mul_(b, d), m));
	}
	let temp_6_0 = (mul_((mul_(b, d)), (mul_(c, c))));
	let temp_6_1 = (mul_((mul_(d, b)), (mul_(c, c))));
	assert(eq_(temp_6_0, temp_6_1)) by {
		cong_mul_(mul_(b, d), mul_(c, c), mul_(d, b), mul_(c, c));
		lemma_mul_comm(b, d);
		lemma_mul_comm(c, c);
	}
	let temp_7_0 = (mod_((mul_((sub_(a, b)), (mul_(d, c)))), m));
	let temp_7_1 = (mod_((mul_((mul_(d, c)), (sub_(a, b)))), m));
	assert(eq_(temp_7_0, temp_7_1)) by {
		lemma_mul_comm(sub_(a, b), mul_(d, c));
		cong_mod_(mul_(sub_(a, b), mul_(d, c)), m, mul_(mul_(d, c), sub_(a, b)), m);
		lemma_eq_ref(m);
	}
	let temp_8_0 = (mul_((mul_(d, (mod_(b, m)))), (mul_(c, a))));
	let temp_8_1 = (mul_(d, (mul_((mod_(b, m)), (mul_(c, a))))));
	assert(eq_(temp_8_0, temp_8_1)) by {
		lemma_mul_assoc(d, mod_(b, m), mul_(c, a));
		lemma_eq_sym(temp_8_1, temp_8_0);
	}
	let temp_9_0 = (mul_((add_(a, b)), (mul_(a, a))));
	let temp_9_1 = (add_((mul_(a, (mul_(a, a)))), (mul_(b, (mul_(a, a))))));
	assert(eq_(temp_9_0, temp_9_1)) by {
		lemma_mul_dist(a, b, mul_(a, a));
	}
	let temp_10_0 = (mul_((mul_(d, d)), (mul_(b, c))));
	let temp_10_1 = (mul_((mul_(b, c)), (mul_(d, d))));
	assert(eq_(temp_10_0, temp_10_1)) by {
		lemma_mul_comm(mul_(d, d), mul_(b, c));
	}
	let temp_11_0 = (sub_((mul_(b, b)), (sub_((mod_(a, m)), a))));
	let temp_11_1 = (sub_((mul_(b, b)), (sub_((mod_((sub_(a, (mul_((add_((mul_(c, a)), (add_(a, a)))), m)))), m)), a))));
	assert(eq_(temp_11_0, temp_11_1)) by {
		lemma_mul_comm(b, b);
		lemma_mod_mul_vanish(a, add_(mul_(c, a), add_(a, a)), m);
		cong_sub_(mul_(b, b), sub_(mod_(a, m), a), mul_(b, b), sub_(mod_(sub_(a, mul_(add_(mul_(c, a), add_(a, a)), m)), m), a));
		cong_sub_(mod_(a, m), a, mod_(sub_(a, mul_(add_(mul_(c, a), add_(a, a)), m)), m), a);
		lemma_eq_ref(a);
	}
	let temp_12_0 = (mul_((mul_(a, a)), (mul_(a, d))));
	let temp_12_1 = (mul_((mul_((mul_(a, a)), a)), d));
	assert(eq_(temp_12_0, temp_12_1)) by {
		lemma_mul_assoc(mul_(a, a), a, d);
	}
	let temp_13_0 = (mul_((mod_((mul_(a, b)), m)), (sub_(a, a))));
	let temp_13_1 = (mul_((sub_(a, a)), (mod_((mul_(a, b)), m))));
	assert(eq_(temp_13_0, temp_13_1)) by {
		lemma_mul_comm(mod_(mul_(a, b), m), sub_(a, a));
	}
	let temp_14_0 = (mul_((mul_(b, a)), (mul_(b, d))));
	let temp_14_1 = (mul_((mul_(b, d)), (mul_(b, a))));
	assert(eq_(temp_14_0, temp_14_1)) by {
		lemma_mul_comm(mul_(b, a), mul_(b, d));
	}
	let temp_15_0 = (add_((sub_(a, a)), (add_(c, c))));
	let temp_15_1 = (add_((sub_(a, a)), (add_(c, c))));
	assert(eq_(temp_15_0, temp_15_1)) by {
		lemma_eq_ref(temp_15_0);
	}
	let temp_16_0 = (mul_((mul_(c, d)), (mul_(c, d))));
	let temp_16_1 = (mul_((mul_(c, d)), (mul_(d, c))));
	assert(eq_(temp_16_0, temp_16_1)) by {
		cong_mul_(mul_(c, d), mul_(c, d), mul_(c, d), mul_(d, c));
		lemma_mul_comm(c, d);
		lemma_eq_ref(mul_(c, d));
	}
	let temp_17_0 = (mul_((mul_(c, b)), (mod_((add_(b, c)), m))));
	let temp_17_1 = (mul_(c, (mul_(b, (mod_((add_(b, c)), m))))));
	assert(eq_(temp_17_0, temp_17_1)) by {
		lemma_eq_sym(temp_17_1, temp_17_0);
		lemma_mul_assoc(c, b, mod_(add_(b, c), m));
	}
	let temp_18_0 = (mul_((mul_(b, a)), (add_(d, d))));
	let temp_18_1 = (add_((mul_((mul_(b, a)), d)), (mul_((mul_(b, a)), d))));
	assert(eq_(temp_18_0, temp_18_1)) by {
		lemma_mul_dist(mul_(b, a), d, d);
	}
	let temp_19_0 = (mod_((mul_((mul_(b, a)), (mod_((mul_(a, a)), m)))), m));
	let temp_19_1 = (mod_((mul_((mul_(b, a)), (mod_((mul_(a, a)), m)))), m));
	assert(eq_(temp_19_0, temp_19_1)) by {
		lemma_eq_ref(temp_19_0);
	}
	let temp_20_0 = (mul_((mul_(a, (mod_(d, m)))), (sub_(a, c))));
	let temp_20_1 = (mul_((mul_((mod_(d, m)), a)), (sub_(a, c))));
	assert(eq_(temp_20_0, temp_20_1)) by {
		lemma_mul_comm(a, mod_(d, m));
		cong_mul_(mul_(a, mod_(d, m)), sub_(a, c), mul_(mod_(d, m), a), sub_(a, c));
		lemma_eq_ref(sub_(a, c));
	}
	let temp_21_0 = (mul_((mul_(d, d)), (sub_(c, d))));
	let temp_21_1 = (mul_(d, (mul_(d, (sub_(c, d))))));
	assert(eq_(temp_21_0, temp_21_1)) by {
		lemma_eq_sym(temp_21_1, temp_21_0);
		lemma_mul_assoc(d, d, sub_(c, d));
	}
	let temp_22_0 = (mod_((mul_((mul_(b, a)), (mul_(b, c)))), m));
	let temp_22_1 = (mod_((mul_((mul_((mul_(b, a)), b)), c)), m));
	assert(eq_(temp_22_0, temp_22_1)) by {
		lemma_mul_assoc(mul_(b, a), b, c);
		cong_mod_(mul_(mul_(b, a), mul_(b, c)), m, mul_(mul_(mul_(b, a), b), c), m);
		lemma_eq_ref(m);
	}
	let temp_23_0 = (mul_((mul_(a, as_elem(30))), (mul_(d, d))));
	let temp_23_1 = (mul_(a, (mul_(as_elem(30), (mul_(d, d))))));
	assert(eq_(temp_23_0, temp_23_1)) by {
		lemma_eq_sym(temp_23_1, temp_23_0);
		lemma_mul_assoc(a, as_elem(30), mul_(d, d));
	}
	let temp_24_0 = (mul_((mul_((mod_(a, m)), c)), (mul_(c, a))));
	let temp_24_1 = (mul_((mul_((mod_((add_((mul_((mul_((mod_((mul_(a, d)), m)), (mul_(a, b)))), m)), a)), m)), c)), (mul_(c, a))));
	assert(eq_(temp_24_0, temp_24_1)) by {
		lemma_mul_comm(c, a);
		lemma_mul_comm(a, c);
		lemma_mod_mul_vanish(a, mul_(mod_(mul_(a, d), m), mul_(a, b)), m);
		cong_mul_(mul_(mod_(a, m), c), mul_(c, a), mul_(mod_(add_(mul_(mul_(mod_(mul_(a, d), m), mul_(a, b)), m), a), m), c), mul_(c, a));
		cong_mul_(mod_(a, m), c, mod_(add_(mul_(mul_(mod_(mul_(a, d), m), mul_(a, b)), m), a), m), c);
		lemma_eq_ref(c);
		lemma_eq_trans(mul_(c, a), mul_(a, c), mul_(c, a));
	}
	let temp_25_0 = (add_((mul_(b, c)), (mul_(c, a))));
	let temp_25_1 = (add_((mul_(c, a)), (mul_(b, c))));
	assert(eq_(temp_25_0, temp_25_1)) by {
		lemma_add_comm(mul_(b, c), mul_(c, a));
	}
	let temp_26_0 = (mul_((mod_((mul_((mod_(b, m)), (mod_(c, m)))), m)), (mul_(d, a))));
	let temp_26_1 = (mul_((mul_((mod_((mul_((mod_(b, m)), (mod_(c, m)))), m)), d)), a));
	assert(eq_(temp_26_0, temp_26_1)) by {
		lemma_mul_assoc(mod_(mul_(mod_(b, m), mod_(c, m)), m), d, a);
	}
	let temp_27_0 = (mul_((sub_(c, d)), (sub_(d, a))));
	let temp_27_1 = (sub_((mul_(c, (sub_(d, a)))), (mul_(d, (sub_(d, a))))));
	assert(eq_(temp_27_0, temp_27_1)) by {
		lemma_mul_dist(sub_(d, a), c, d);
	}
	let temp_28_0 = (add_((mul_(a, c)), (mod_((mul_(c, c)), m))));
	let temp_28_1 = (add_((mul_(a, c)), (mod_((mul_(c, c)), m))));
	assert(eq_(temp_28_0, temp_28_1)) by {
		lemma_eq_ref(temp_28_0);
	}
	let temp_29_0 = (sub_((sub_(b, d)), (mul_((mod_(b, m)), d))));
	let temp_29_1 = (sub_((sub_(b, d)), (mul_((mod_((sub_(b, (mul_((mul_((mul_((mod_(d, m)), d)), (add_(c, (mod_(b, m)))))), m)))), m)), d))));
	assert(eq_(temp_29_0, temp_29_1)) by {
		lemma_mod_mul_vanish(b, mul_(mul_(mod_(d, m), d), add_(c, mod_(b, m))), m);
		cong_sub_(sub_(b, d), mul_(mod_(b, m), d), sub_(b, d), mul_(mod_(sub_(b, mul_(mul_(mul_(mod_(d, m), d), add_(c, mod_(b, m))), m)), m), d));
		lemma_eq_ref(d);
		cong_mul_(mod_(b, m), d, mod_(sub_(b, mul_(mul_(mul_(mod_(d, m), d), add_(c, mod_(b, m))), m)), m), d);
		lemma_eq_ref(sub_(b, d));
	}
	let temp_30_0 = (mod_((mul_((mul_(b, d)), (mod_((mul_(d, c)), m)))), m));
	let temp_30_1 = (mod_((mul_((mul_(b, d)), (mod_((mul_(c, d)), m)))), m));
	assert(eq_(temp_30_0, temp_30_1)) by {
		lemma_mul_comm(d, c);
		cong_mod_(mul_(mul_(b, d), mod_(mul_(d, c), m)), m, mul_(mul_(b, d), mod_(mul_(c, d), m)), m);
		lemma_eq_ref(m);
		lemma_eq_ref(mul_(b, d));
		cong_mod_(mul_(d, c), m, mul_(c, d), m);
		cong_mul_(mul_(b, d), mod_(mul_(d, c), m), mul_(b, d), mod_(mul_(c, d), m));
	}
	let temp_31_0 = (mul_((mul_(c, b)), (mul_(a, (mod_(d, m))))));
	let temp_31_1 = (mul_((mul_(c, b)), (mul_((mod_(d, m)), a))));
	assert(eq_(temp_31_0, temp_31_1)) by {
		lemma_mul_comm(a, mod_(d, m));
		cong_mul_(mul_(c, b), mul_(a, mod_(d, m)), mul_(c, b), mul_(mod_(d, m), a));
		lemma_eq_ref(mul_(c, b));
	}
	let temp_32_0 = (mod_((add_((mul_(c, a)), (mul_(c, d)))), m));
	let temp_32_1 = (mod_((add_((mul_(c, a)), (mul_(d, c)))), m));
	assert(eq_(temp_32_0, temp_32_1)) by {
		lemma_mul_comm(c, d);
		cong_mod_(add_(mul_(c, a), mul_(c, d)), m, add_(mul_(c, a), mul_(d, c)), m);
		lemma_eq_ref(mul_(c, a));
		cong_add_(mul_(c, a), mul_(c, d), mul_(c, a), mul_(d, c));
		lemma_eq_ref(m);
	}
	let temp_33_0 = (mod_((sub_((mul_(b, (mod_(c, m)))), (mul_((mod_(d, m)), c)))), m));
	let temp_33_1 = (mod_((sub_((mod_((mul_(b, (mod_(c, m)))), m)), (mul_((mod_(d, m)), c)))), m));
	assert(eq_(temp_33_0, temp_33_1)) by {
		lemma_mod_sub_noop(mul_(b, mod_(c, m)), mul_(mod_(d, m), c), m);
	}
	let temp_34_0 = (sub_((add_(c, a)), (mul_(b, b))));
	let temp_34_1 = (sub_((add_(a, c)), (mul_(b, b))));
	assert(eq_(temp_34_0, temp_34_1)) by {
		cong_sub_(add_(c, a), mul_(b, b), add_(a, c), mul_(b, b));
		lemma_add_comm(c, a);
		lemma_mul_comm(b, b);
	}
	let temp_35_0 = (mul_((mul_((mod_(c, m)), c)), (mul_(a, c))));
	let temp_35_1 = (mul_((mul_((mod_((add_(c, (mul_((mod_((mul_((mod_((mul_(a, c)), m)), (mul_(b, d)))), m)), m)))), m)), c)), (mul_(a, c))));
	assert(eq_(temp_35_0, temp_35_1)) by {
		lemma_mod_mul_vanish(c, mod_(mul_(mod_(mul_(a, c), m), mul_(b, d)), m), m);
		cong_mul_(mul_(mod_(c, m), c), mul_(a, c), mul_(mod_(add_(c, mul_(mod_(mul_(mod_(mul_(a, c), m), mul_(b, d)), m), m)), m), c), mul_(a, c));
		lemma_eq_ref(c);
		cong_mul_(mod_(c, m), c, mod_(add_(c, mul_(mod_(mul_(mod_(mul_(a, c), m), mul_(b, d)), m), m)), m), c);
		lemma_eq_ref(mul_(a, c));
	}
	let temp_36_0 = (mul_((mul_(d, a)), (mul_(d, (mod_(as_elem(56), m))))));
	let temp_36_1 = (mul_((mul_(d, a)), (mul_((mod_(as_elem(56), m)), d))));
	assert(eq_(temp_36_0, temp_36_1)) by {
		lemma_mul_comm(d, mod_(as_elem(56), m));
		cong_mul_(mul_(d, a), mul_(d, mod_(as_elem(56), m)), mul_(d, a), mul_(mod_(as_elem(56), m), d));
		lemma_eq_ref(mul_(d, a));
	}
	let temp_37_0 = (mul_((mul_((mod_(d, m)), c)), (mod_((mul_(as_elem(64), c)), m))));
	let temp_37_1 = (mul_((mod_(d, m)), (mul_(c, (mod_((mul_(as_elem(64), c)), m))))));
	assert(eq_(temp_37_0, temp_37_1)) by {
		lemma_mul_assoc(mod_(d, m), c, mod_(mul_(as_elem(64), c), m));
		lemma_eq_sym(temp_37_1, temp_37_0);
	}
	let temp_38_0 = (mul_((mul_(d, b)), (mul_(d, (mod_(b, m))))));
	let temp_38_1 = (mul_((mul_((mul_(d, b)), d)), (mod_(b, m))));
	assert(eq_(temp_38_0, temp_38_1)) by {
		lemma_mul_assoc(mul_(d, b), d, mod_(b, m));
	}
	let temp_39_0 = (add_((mod_((add_(d, (mod_(as_elem(9), m)))), m)), (sub_(a, d))));
	let temp_39_1 = (add_((mod_((add_((mod_(as_elem(9), m)), d)), m)), (sub_(a, d))));
	assert(eq_(temp_39_0, temp_39_1)) by {
		lemma_add_comm(d, mod_(as_elem(9), m));
		cong_add_(mod_(add_(d, mod_(as_elem(9), m)), m), sub_(a, d), mod_(add_(mod_(as_elem(9), m), d), m), sub_(a, d));
		lemma_eq_ref(m);
		cong_mod_(add_(d, mod_(as_elem(9), m)), m, add_(mod_(as_elem(9), m), d), m);
		lemma_eq_ref(sub_(a, d));
	}
	let temp_40_0 = (mul_((add_(a, d)), (sub_(d, c))));
	let temp_40_1 = (mul_((sub_(d, c)), (add_(a, d))));
	assert(eq_(temp_40_0, temp_40_1)) by {
		lemma_mul_comm(add_(a, d), sub_(d, c));
	}
	let temp_41_0 = (mul_((mul_(a, c)), (mul_(b, c))));
	let temp_41_1 = (mul_((mul_(c, a)), (mul_(b, c))));
	assert(eq_(temp_41_0, temp_41_1)) by {
		cong_mul_(mul_(a, c), mul_(b, c), mul_(c, a), mul_(b, c));
		lemma_mul_comm(a, c);
		lemma_eq_ref(mul_(b, c));
	}
	let temp_42_0 = (add_((mul_(c, c)), (mod_((mul_(b, b)), m))));
	let temp_42_1 = (add_((mod_((mul_(b, b)), m)), (mul_(c, c))));
	assert(eq_(temp_42_0, temp_42_1)) by {
		lemma_add_comm(mul_(c, c), mod_(mul_(b, b), m));
	}
	let temp_43_0 = (mul_((mul_(a, b)), (mul_(b, b))));
	let temp_43_1 = (mul_((mul_(a, b)), (mul_(b, b))));
	assert(eq_(temp_43_0, temp_43_1)) by {
		lemma_eq_ref(temp_43_0);
	}
	let temp_44_0 = (mul_((mul_(a, b)), (sub_(d, d))));
	let temp_44_1 = (mul_(a, (mul_(b, (sub_(d, d))))));
	assert(eq_(temp_44_0, temp_44_1)) by {
		lemma_eq_sym(temp_44_1, temp_44_0);
		lemma_mul_assoc(a, b, sub_(d, d));
	}
	let temp_45_0 = (mul_((mul_(a, b)), (add_(b, c))));
	let temp_45_1 = (mul_(a, (mul_(b, (add_(b, c))))));
	assert(eq_(temp_45_0, temp_45_1)) by {
		lemma_eq_sym(temp_45_1, temp_45_0);
		lemma_mul_assoc(a, b, add_(b, c));
	}
	let temp_46_0 = (mod_((add_((sub_(d, c)), (sub_(a, b)))), m));
	let temp_46_1 = (mod_((add_((add_((sub_(d, c)), (sub_(a, b)))), (mul_((mul_((mod_((mul_(a, a)), m)), (add_((mod_(d, m)), (mod_(d, m)))))), m)))), m));
	assert(eq_(temp_46_0, temp_46_1)) by {
		lemma_mod_mul_vanish(add_(sub_(d, c), sub_(a, b)), mul_(mod_(mul_(a, a), m), add_(mod_(d, m), mod_(d, m))), m);
	}
	let temp_47_0 = (mul_((mul_(a, a)), (add_(a, c))));
	let temp_47_1 = (mul_(a, (mul_(a, (add_(a, c))))));
	assert(eq_(temp_47_0, temp_47_1)) by {
		lemma_eq_sym(temp_47_1, temp_47_0);
		lemma_mul_assoc(a, a, add_(a, c));
	}
	let temp_48_0 = (mul_((mul_(b, c)), (add_(b, a))));
	let temp_48_1 = (mul_((mul_(b, c)), (add_(a, b))));
	assert(eq_(temp_48_0, temp_48_1)) by {
		cong_mul_(mul_(b, c), add_(b, a), mul_(b, c), add_(a, b));
		lemma_add_comm(b, a);
		lemma_eq_ref(mul_(b, c));
	}
	let temp_49_0 = (mul_((mul_(c, a)), (mul_(b, d))));
	let temp_49_1 = (mul_(c, (mul_(a, (mul_(b, d))))));
	assert(eq_(temp_49_0, temp_49_1)) by {
		lemma_eq_sym(temp_49_1, temp_49_0);
		lemma_mul_assoc(c, a, mul_(b, d));
	}
	let temp_50_0 = (mul_((mul_(b, a)), (mul_(b, c))));
	let temp_50_1 = (mul_((mul_((mul_(b, a)), b)), c));
	assert(eq_(temp_50_0, temp_50_1)) by {
		lemma_mul_assoc(mul_(b, a), b, c);
	}
	let temp_51_0 = (mul_((mul_(b, d)), (mod_((mul_(d, a)), m))));
	let temp_51_1 = (mul_((mul_(b, d)), (mod_((add_((mul_(d, a)), (mul_((mul_((mul_(d, b)), (mod_((mul_(a, a)), m)))), m)))), m))));
	assert(eq_(temp_51_0, temp_51_1)) by {
		lemma_mod_mul_vanish(mul_(d, a), mul_(mul_(d, b), mod_(mul_(a, a), m)), m);
		cong_mul_(mul_(b, d), mod_(mul_(d, a), m), mul_(b, d), mod_(add_(mul_(d, a), mul_(mul_(mul_(d, b), mod_(mul_(a, a), m)), m)), m));
		lemma_eq_ref(mul_(b, d));
	}
	let temp_52_0 = (mul_((mul_((mod_(d, m)), c)), (sub_(as_elem(23), a))));
	let temp_52_1 = (mul_((mod_(d, m)), (mul_(c, (sub_(as_elem(23), a))))));
	assert(eq_(temp_52_0, temp_52_1)) by {
		lemma_mul_assoc(mod_(d, m), c, sub_(as_elem(23), a));
		lemma_eq_sym(temp_52_1, temp_52_0);
	}
	let temp_53_0 = (mod_((mul_((mul_(a, d)), (sub_((mod_(d, m)), c)))), m));
	let temp_53_1 = (mod_((mul_((mul_(a, d)), (sub_((mod_((sub_(d, (mul_((mul_((mul_(d, b)), (sub_((mod_(b, m)), a)))), m)))), m)), c)))), m));
	assert(eq_(temp_53_0, temp_53_1)) by {
		lemma_mod_mul_vanish(d, mul_(mul_(d, b), sub_(mod_(b, m), a)), m);
		cong_mod_(mul_(mul_(a, d), sub_(mod_(d, m), c)), m, mul_(mul_(a, d), sub_(mod_(sub_(d, mul_(mul_(mul_(d, b), sub_(mod_(b, m), a)), m)), m), c)), m);
		cong_mul_(mul_(a, d), sub_(mod_(d, m), c), mul_(a, d), sub_(mod_(sub_(d, mul_(mul_(mul_(d, b), sub_(mod_(b, m), a)), m)), m), c));
		lemma_eq_ref(mul_(a, d));
		cong_sub_(mod_(d, m), c, mod_(sub_(d, mul_(mul_(mul_(d, b), sub_(mod_(b, m), a)), m)), m), c);
		lemma_eq_ref(c);
		lemma_eq_ref(m);
	}
	let temp_54_0 = (mod_((sub_((mul_(d, (mod_(b, m)))), (mul_((mod_(b, m)), d)))), m));
	let temp_54_1 = (mod_((sub_((mul_(d, (mod_(b, m)))), (mod_((mul_((mod_(b, m)), d)), m)))), m));
	assert(eq_(temp_54_0, temp_54_1)) by {
		lemma_mod_sub_noop(mul_(d, mod_(b, m)), mul_(mod_(b, m), d), m);
	}
	let temp_55_0 = (mul_((mul_(a, a)), (mul_(b, b))));
	let temp_55_1 = (mul_((mul_(a, a)), (mul_(b, b))));
	assert(eq_(temp_55_0, temp_55_1)) by {
		lemma_eq_ref(temp_55_0);
	}
	let temp_56_0 = (add_((mul_((mod_(b, m)), c)), (mul_(d, d))));
	let temp_56_1 = (add_((mul_((mod_((sub_(b, (mul_((sub_((sub_(d, c)), (mul_(a, a)))), m)))), m)), c)), (mul_(d, d))));
	assert(eq_(temp_56_0, temp_56_1)) by {
		lemma_mod_mul_vanish(b, sub_(sub_(d, c), mul_(a, a)), m);
		cong_add_(mul_(mod_(b, m), c), mul_(d, d), mul_(mod_(sub_(b, mul_(sub_(sub_(d, c), mul_(a, a)), m)), m), c), mul_(d, d));
		cong_mul_(mod_(b, m), c, mod_(sub_(b, mul_(sub_(sub_(d, c), mul_(a, a)), m)), m), c);
		lemma_eq_ref(mul_(d, d));
		lemma_eq_ref(c);
	}
	let temp_57_0 = (mul_((mul_(a, a)), (mul_(a, c))));
	let temp_57_1 = (mul_((mul_(a, c)), (mul_(a, a))));
	assert(eq_(temp_57_0, temp_57_1)) by {
		lemma_mul_comm(mul_(a, a), mul_(a, c));
	}
	let temp_58_0 = (sub_((mod_((mul_(b, c)), m)), (sub_((mod_(a, m)), d))));
	let temp_58_1 = (sub_((mod_((mul_(c, b)), m)), (sub_((mod_(a, m)), d))));
	assert(eq_(temp_58_0, temp_58_1)) by {
		lemma_mul_comm(b, c);
		cong_sub_(mod_(mul_(b, c), m), sub_(mod_(a, m), d), mod_(mul_(c, b), m), sub_(mod_(a, m), d));
		cong_mod_(mul_(b, c), m, mul_(c, b), m);
		lemma_eq_ref(sub_(mod_(a, m), d));
		lemma_eq_ref(m);
	}
	let temp_59_0 = (add_((mul_((mod_(a, m)), d)), (mul_(a, b))));
	let temp_59_1 = (add_((mul_(a, b)), (mul_((mod_(a, m)), d))));
	assert(eq_(temp_59_0, temp_59_1)) by {
		lemma_add_comm(mul_(mod_(a, m), d), mul_(a, b));
	}
	let temp_60_0 = (mul_((mul_(d, b)), (mul_(d, a))));
	let temp_60_1 = (mul_(d, (mul_(b, (mul_(d, a))))));
	assert(eq_(temp_60_0, temp_60_1)) by {
		lemma_eq_sym(temp_60_1, temp_60_0);
		lemma_mul_assoc(d, b, mul_(d, a));
	}
	let temp_61_0 = (mul_((mul_(b, d)), (add_(b, (mod_(b, m))))));
	let temp_61_1 = (mul_((mul_(b, d)), (add_((mod_(b, m)), b))));
	assert(eq_(temp_61_0, temp_61_1)) by {
		lemma_add_comm(b, mod_(b, m));
		cong_mul_(mul_(b, d), add_(b, mod_(b, m)), mul_(b, d), add_(mod_(b, m), b));
		lemma_eq_ref(mul_(b, d));
	}
	let temp_62_0 = (sub_((mod_((mul_(d, a)), m)), (mul_(a, a))));
	let temp_62_1 = (sub_((mod_((sub_((mul_(d, a)), (mul_((mul_((add_(b, a)), (mul_(d, c)))), m)))), m)), (mul_(a, a))));
	assert(eq_(temp_62_0, temp_62_1)) by {
		lemma_mul_comm(a, a);
		lemma_mod_mul_vanish(mul_(d, a), mul_(add_(b, a), mul_(d, c)), m);
		cong_sub_(mod_(mul_(d, a), m), mul_(a, a), mod_(sub_(mul_(d, a), mul_(mul_(add_(b, a), mul_(d, c)), m)), m), mul_(a, a));
	}
	let temp_63_0 = (mul_((mul_(b, c)), (mul_(b, c))));
	let temp_63_1 = (mul_((mul_(b, c)), (mul_(c, b))));
	assert(eq_(temp_63_0, temp_63_1)) by {
		cong_mul_(mul_(b, c), mul_(b, c), mul_(b, c), mul_(c, b));
		lemma_mul_comm(b, c);
		lemma_eq_ref(mul_(b, c));
	}
	let temp_64_0 = (mul_((mul_(c, a)), (mul_(d, a))));
	let temp_64_1 = (mul_((mul_(a, c)), (mul_(d, a))));
	assert(eq_(temp_64_0, temp_64_1)) by {
		cong_mul_(mul_(c, a), mul_(d, a), mul_(a, c), mul_(d, a));
		lemma_mul_comm(c, a);
		lemma_eq_ref(mul_(d, a));
	}
	let temp_65_0 = (sub_((mul_(a, (mod_(a, m)))), (mul_(a, a))));
	let temp_65_1 = (sub_((mul_((mod_(a, m)), a)), (mul_(a, a))));
	assert(eq_(temp_65_0, temp_65_1)) by {
		cong_sub_(mul_(a, mod_(a, m)), mul_(a, a), mul_(mod_(a, m), a), mul_(a, a));
		lemma_mul_comm(a, mod_(a, m));
		lemma_mul_comm(a, a);
	}
	let temp_66_0 = (mul_((mul_(a, c)), (mul_(b, b))));
	let temp_66_1 = (mul_((mul_(b, b)), (mul_(a, c))));
	assert(eq_(temp_66_0, temp_66_1)) by {
		lemma_mul_comm(mul_(a, c), mul_(b, b));
	}
	let temp_67_0 = (add_((mul_(b, c)), (mul_((mod_(d, m)), (mod_(a, m))))));
	let temp_67_1 = (add_((mul_((mod_(d, m)), (mod_(a, m)))), (mul_(b, c))));
	assert(eq_(temp_67_0, temp_67_1)) by {
		lemma_add_comm(mul_(b, c), mul_(mod_(d, m), mod_(a, m)));
	}
	let temp_68_0 = (mul_((mul_((mod_(a, m)), d)), (mul_(d, c))));
	let temp_68_1 = (mul_((mul_((mul_((mod_(a, m)), d)), d)), c));
	assert(eq_(temp_68_0, temp_68_1)) by {
		lemma_mul_assoc(mul_(mod_(a, m), d), d, c);
	}
	let temp_69_0 = (sub_((mul_(d, d)), (mod_((mul_(b, d)), m))));
	let temp_69_1 = (sub_((mul_(d, d)), (mod_((add_((mul_((mul_(c, (mul_(b, d)))), m)), (mul_(b, d)))), m))));
	assert(eq_(temp_69_0, temp_69_1)) by {
		lemma_mul_comm(d, d);
		lemma_mod_mul_vanish(mul_(b, d), mul_(c, mul_(b, d)), m);
		cong_sub_(mul_(d, d), mod_(mul_(b, d), m), mul_(d, d), mod_(add_(mul_(mul_(c, mul_(b, d)), m), mul_(b, d)), m));
	}
	let temp_70_0 = (mul_((mul_(d, (mod_(a, m)))), (mod_((mul_(a, d)), m))));
	let temp_70_1 = (mul_(d, (mul_((mod_(a, m)), (mod_((mul_(a, d)), m))))));
	assert(eq_(temp_70_0, temp_70_1)) by {
		lemma_mul_assoc(d, mod_(a, m), mod_(mul_(a, d), m));
		lemma_eq_sym(temp_70_1, temp_70_0);
	}
	let temp_71_0 = (mul_((mod_((mul_(b, b)), m)), (mod_((mul_(a, a)), m))));
	let temp_71_1 = (mul_((mod_((mul_(b, b)), m)), (mod_((mul_(a, a)), m))));
	assert(eq_(temp_71_0, temp_71_1)) by {
		lemma_eq_ref(temp_71_0);
	}
	let temp_72_0 = (sub_((sub_(c, a)), (mul_(d, d))));
	let temp_72_1 = (sub_((sub_(c, a)), (mul_(d, d))));
	assert(eq_(temp_72_0, temp_72_1)) by {
		lemma_eq_ref(temp_72_0);
	}
	let temp_73_0 = (mul_((mul_(d, a)), (mul_((mod_(a, m)), d))));
	let temp_73_1 = (mul_((mul_(d, a)), (mul_(d, (mod_(a, m))))));
	assert(eq_(temp_73_0, temp_73_1)) by {
		cong_mul_(mul_(d, a), mul_(mod_(a, m), d), mul_(d, a), mul_(d, mod_(a, m)));
		lemma_mul_comm(mod_(a, m), d);
		lemma_eq_ref(mul_(d, a));
	}
	let temp_74_0 = (mul_((mul_(d, as_elem(75))), c));
	let temp_74_1 = (mul_(d, (mul_(as_elem(75), c))));
	assert(eq_(temp_74_0, temp_74_1)) by {
		lemma_eq_sym(temp_74_1, temp_74_0);
		lemma_mul_assoc(d, as_elem(75), c);
	}
	let temp_75_0 = (mul_((mul_(c, c)), (mul_((mod_(a, m)), (mod_(b, m))))));
	let temp_75_1 = (mul_(c, (mul_(c, (mul_((mod_(a, m)), (mod_(b, m))))))));
	assert(eq_(temp_75_0, temp_75_1)) by {
		lemma_mul_assoc(c, c, mul_(mod_(a, m), mod_(b, m)));
		lemma_eq_sym(temp_75_1, temp_75_0);
	}
	let temp_76_0 = (mul_((mul_(a, (mod_(b, m)))), (mul_(d, a))));
	let temp_76_1 = (mul_((mul_(a, (mod_((sub_(b, (mul_((add_((mul_(b, c)), (mul_(d, b)))), m)))), m)))), (mul_(d, a))));
	assert(eq_(temp_76_0, temp_76_1)) by {
		lemma_mod_mul_vanish(b, add_(mul_(b, c), mul_(d, b)), m);
		cong_mul_(mul_(a, mod_(b, m)), mul_(d, a), mul_(a, mod_(sub_(b, mul_(add_(mul_(b, c), mul_(d, b)), m)), m)), mul_(d, a));
		lemma_eq_ref(a);
		cong_mul_(a, mod_(b, m), a, mod_(sub_(b, mul_(add_(mul_(b, c), mul_(d, b)), m)), m));
		lemma_eq_ref(mul_(d, a));
	}
	let temp_77_0 = (mul_((mul_(b, a)), (add_(as_elem(13), (mod_(a, m))))));
	let temp_77_1 = (mul_((mul_(b, a)), (add_(as_elem(13), (mod_((sub_(a, (mul_((mul_((add_(a, b)), (mul_(c, a)))), m)))), m))))));
	assert(eq_(temp_77_0, temp_77_1)) by {
		lemma_mod_mul_vanish(a, mul_(add_(a, b), mul_(c, a)), m);
		cong_mul_(mul_(b, a), add_(as_elem(13), mod_(a, m)), mul_(b, a), add_(as_elem(13), mod_(sub_(a, mul_(mul_(add_(a, b), mul_(c, a)), m)), m)));
		lemma_eq_ref(mul_(b, a));
		cong_add_(as_elem(13), mod_(a, m), as_elem(13), mod_(sub_(a, mul_(mul_(add_(a, b), mul_(c, a)), m)), m));
		lemma_eq_ref(as_elem(13));
	}
	let temp_78_0 = (mul_((add_(c, (mod_(c, m)))), (mul_(b, c))));
	let temp_78_1 = (mul_((add_(c, (mod_(c, m)))), (mul_(c, b))));
	assert(eq_(temp_78_0, temp_78_1)) by {
		cong_mul_(add_(c, mod_(c, m)), mul_(b, c), add_(c, mod_(c, m)), mul_(c, b));
		lemma_mul_comm(b, c);
		lemma_eq_ref(add_(c, mod_(c, m)));
	}
	let temp_79_0 = (add_((mul_(a, d)), (mod_((mul_(d, d)), m))));
	let temp_79_1 = (add_((mul_(d, a)), (mod_((mul_(d, d)), m))));
	assert(eq_(temp_79_0, temp_79_1)) by {
		cong_add_(mul_(a, d), mod_(mul_(d, d), m), mul_(d, a), mod_(mul_(d, d), m));
		lemma_mul_comm(a, d);
		lemma_eq_ref(mod_(mul_(d, d), m));
	}
	let temp_80_0 = (sub_((mul_(c, c)), (mul_(d, (mod_(a, m))))));
	let temp_80_1 = (sub_((mul_(c, c)), (mul_(d, (mod_((add_((mul_((mul_((mul_(d, a)), (mul_(b, (mod_(b, m)))))), m)), a)), m))))));
	assert(eq_(temp_80_0, temp_80_1)) by {
		lemma_mul_comm(c, c);
		lemma_mod_mul_vanish(a, mul_(mul_(d, a), mul_(b, mod_(b, m))), m);
		cong_sub_(mul_(c, c), mul_(d, mod_(a, m)), mul_(c, c), mul_(d, mod_(add_(mul_(mul_(mul_(d, a), mul_(b, mod_(b, m))), m), a), m)));
		lemma_eq_ref(d);
		cong_mul_(d, mod_(a, m), d, mod_(add_(mul_(mul_(mul_(d, a), mul_(b, mod_(b, m))), m), a), m));
	}
	let temp_81_0 = (mul_((mul_(as_elem(78), b)), (mul_(d, a))));
	let temp_81_1 = (mul_((mul_(b, as_elem(78))), (mul_(d, a))));
	assert(eq_(temp_81_0, temp_81_1)) by {
		lemma_mul_comm(as_elem(78), b);
		cong_mul_(mul_(as_elem(78), b), mul_(d, a), mul_(b, as_elem(78)), mul_(d, a));
		lemma_eq_ref(mul_(d, a));
	}
	let temp_82_0 = (mul_((mul_(c, c)), (add_((mod_(b, m)), a))));
	let temp_82_1 = (add_((mul_((mul_(c, c)), (mod_(b, m)))), (mul_((mul_(c, c)), a))));
	assert(eq_(temp_82_0, temp_82_1)) by {
		lemma_mul_dist(mul_(c, c), mod_(b, m), a);
	}
	let temp_83_0 = (mul_((mul_(c, a)), (mul_(c, d))));
	let temp_83_1 = (mul_((mul_(c, d)), (mul_(c, a))));
	assert(eq_(temp_83_0, temp_83_1)) by {
		lemma_mul_comm(mul_(c, a), mul_(c, d));
	}
	let temp_84_0 = (sub_((mul_(b, a)), (sub_(as_elem(24), d))));
	let temp_84_1 = (sub_((mul_(a, b)), (sub_(as_elem(24), d))));
	assert(eq_(temp_84_0, temp_84_1)) by {
		lemma_mul_comm(b, a);
		cong_sub_(mul_(b, a), sub_(as_elem(24), d), mul_(a, b), sub_(as_elem(24), d));
		lemma_eq_ref(sub_(as_elem(24), d));
	}
	let temp_85_0 = (mul_((mul_(d, c)), (sub_((mod_(c, m)), (mod_(c, m))))));
	let temp_85_1 = (mul_((sub_((mod_(c, m)), (mod_(c, m)))), (mul_(d, c))));
	assert(eq_(temp_85_0, temp_85_1)) by {
		lemma_mul_comm(mul_(d, c), sub_(mod_(c, m), mod_(c, m)));
	}
	let temp_86_0 = (mul_((mul_(d, d)), (mul_(d, d))));
	let temp_86_1 = (mul_(d, (mul_(d, (mul_(d, d))))));
	assert(eq_(temp_86_0, temp_86_1)) by {
		lemma_eq_sym(temp_86_1, temp_86_0);
		lemma_mul_assoc(d, d, mul_(d, d));
	}
	let temp_87_0 = (mul_((mul_(b, c)), (mul_(b, a))));
	let temp_87_1 = (mul_((mul_(b, c)), (mul_(a, b))));
	assert(eq_(temp_87_0, temp_87_1)) by {
		cong_mul_(mul_(b, c), mul_(b, a), mul_(b, c), mul_(a, b));
		lemma_mul_comm(b, a);
		lemma_eq_ref(mul_(b, c));
	}
	let temp_88_0 = (mul_((mul_(b, c)), (add_((mod_(b, m)), d))));
	let temp_88_1 = (mul_((mul_(b, c)), (add_(d, (mod_(b, m))))));
	assert(eq_(temp_88_0, temp_88_1)) by {
		lemma_add_comm(mod_(b, m), d);
		cong_mul_(mul_(b, c), add_(mod_(b, m), d), mul_(b, c), add_(d, mod_(b, m)));
		lemma_eq_ref(mul_(b, c));
	}
	let temp_89_0 = (mul_((mul_(a, d)), (mul_(d, a))));
	let temp_89_1 = (mul_((mul_((mul_(a, d)), d)), a));
	assert(eq_(temp_89_0, temp_89_1)) by {
		lemma_mul_assoc(mul_(a, d), d, a);
	}
	let temp_90_0 = (mul_((add_((mod_(d, m)), d)), (mul_(c, c))));
	let temp_90_1 = (mul_((mul_((add_((mod_(d, m)), d)), c)), c));
	assert(eq_(temp_90_0, temp_90_1)) by {
		lemma_mul_assoc(add_(mod_(d, m), d), c, c);
	}
	let temp_91_0 = (mul_((mul_((mod_(a, m)), c)), (mul_(a, a))));
	let temp_91_1 = (mul_((mul_((mod_((add_(a, (mul_((mul_((mul_(d, a)), (sub_(d, b)))), m)))), m)), c)), (mul_(a, a))));
	assert(eq_(temp_91_0, temp_91_1)) by {
		lemma_mul_comm(a, a);
		lemma_mod_mul_vanish(a, mul_(mul_(d, a), sub_(d, b)), m);
		cong_mul_(mul_(mod_(a, m), c), mul_(a, a), mul_(mod_(add_(a, mul_(mul_(mul_(d, a), sub_(d, b)), m)), m), c), mul_(a, a));
		lemma_eq_ref(c);
		cong_mul_(mod_(a, m), c, mod_(add_(a, mul_(mul_(mul_(d, a), sub_(d, b)), m)), m), c);
	}
	let temp_92_0 = (sub_((mod_((mul_(b, a)), m)), (mul_(c, c))));
	let temp_92_1 = (sub_((mod_((add_((mul_(b, a)), (mul_((mul_((mul_(a, a)), (mul_(b, a)))), m)))), m)), (mul_(c, c))));
	assert(eq_(temp_92_0, temp_92_1)) by {
		lemma_mul_comm(c, c);
		lemma_mod_mul_vanish(mul_(b, a), mul_(mul_(a, a), mul_(b, a)), m);
		cong_sub_(mod_(mul_(b, a), m), mul_(c, c), mod_(add_(mul_(b, a), mul_(mul_(mul_(a, a), mul_(b, a)), m)), m), mul_(c, c));
	}
	let temp_93_0 = (mul_((mul_(as_elem(56), d)), (mul_(b, d))));
	let temp_93_1 = (mul_((mul_((mul_(as_elem(56), d)), b)), d));
	assert(eq_(temp_93_0, temp_93_1)) by {
		lemma_mul_assoc(mul_(as_elem(56), d), b, d);
	}
	let temp_94_0 = (sub_((mul_((mod_(b, m)), a)), (mul_(c, c))));
	let temp_94_1 = (sub_((mul_((mod_((sub_(b, (mul_((mul_(c, (add_(c, d)))), m)))), m)), a)), (mul_(c, c))));
	assert(eq_(temp_94_0, temp_94_1)) by {
		lemma_mul_comm(c, c);
		lemma_mod_mul_vanish(b, mul_(c, add_(c, d)), m);
		cong_sub_(mul_(mod_(b, m), a), mul_(c, c), mul_(mod_(sub_(b, mul_(mul_(c, add_(c, d)), m)), m), a), mul_(c, c));
		cong_mul_(mod_(b, m), a, mod_(sub_(b, mul_(mul_(c, add_(c, d)), m)), m), a);
		lemma_eq_ref(a);
	}
	let temp_95_0 = (mod_((sub_((mod_((mul_(d, b)), m)), (mul_(d, b)))), m));
	let temp_95_1 = (mod_((sub_((mod_((mul_(d, b)), m)), (mul_(b, d)))), m));
	assert(eq_(temp_95_0, temp_95_1)) by {
		lemma_mul_comm(d, b);
		cong_mod_(sub_(mod_(mul_(d, b), m), mul_(d, b)), m, sub_(mod_(mul_(d, b), m), mul_(b, d)), m);
		cong_sub_(mod_(mul_(d, b), m), mul_(d, b), mod_(mul_(d, b), m), mul_(b, d));
		lemma_eq_ref(m);
		lemma_eq_ref(mod_(mul_(d, b), m));
	}
	let temp_96_0 = (mul_((mul_(c, c)), (mul_(a, c))));
	let temp_96_1 = (mul_((mul_((mul_(c, c)), a)), c));
	assert(eq_(temp_96_0, temp_96_1)) by {
		lemma_mul_assoc(mul_(c, c), a, c);
	}
	let temp_97_0 = (mul_((mul_(as_elem(95), d)), (mul_(b, a))));
	let temp_97_1 = (mul_((mul_((mul_(as_elem(95), d)), b)), a));
	assert(eq_(temp_97_0, temp_97_1)) by {
		lemma_mul_assoc(mul_(as_elem(95), d), b, a);
	}
	let temp_98_0 = (mul_((mul_(b, d)), (mul_(b, b))));
	let temp_98_1 = (mul_((mul_((mul_(b, d)), b)), b));
	assert(eq_(temp_98_0, temp_98_1)) by {
		lemma_mul_assoc(mul_(b, d), b, b);
	}
	let temp_99_0 = (mod_((mul_((mul_(d, c)), (mul_(c, a)))), m));
	let temp_99_1 = (mod_((mul_((mul_(d, c)), (mul_(a, c)))), m));
	assert(eq_(temp_99_0, temp_99_1)) by {
		lemma_mul_comm(c, a);
		cong_mod_(mul_(mul_(d, c), mul_(c, a)), m, mul_(mul_(d, c), mul_(a, c)), m);
		lemma_eq_ref(mul_(d, c));
		cong_mul_(mul_(d, c), mul_(c, a), mul_(d, c), mul_(a, c));
		lemma_eq_ref(m);
	}
	let temp_100_0 = (add_((mod_((add_(c, b)), m)), (sub_((mod_(b, m)), c))));
	let temp_100_1 = (add_((mod_((add_(b, c)), m)), (sub_((mod_(b, m)), c))));
	assert(eq_(temp_100_0, temp_100_1)) by {
		lemma_eq_sym(add_(b, c), add_(c, b));
		lemma_add_comm(b, c);
		cong_add_(mod_(add_(c, b), m), sub_(mod_(b, m), c), mod_(add_(b, c), m), sub_(mod_(b, m), c));
		lemma_eq_ref(m);
		cong_mod_(add_(c, b), m, add_(b, c), m);
		lemma_eq_ref(sub_(mod_(b, m), c));
	}
	let temp_101_0 = (mul_((mul_(a, a)), (mul_(as_elem(91), b))));
	let temp_101_1 = (mul_((mul_((mul_(a, a)), as_elem(91))), b));
	assert(eq_(temp_101_0, temp_101_1)) by {
		lemma_mul_assoc(mul_(a, a), as_elem(91), b);
	}
	let temp_102_0 = (mul_((mul_(a, d)), (mul_((mod_(d, m)), d))));
	let temp_102_1 = (mul_((mul_((mul_(a, d)), (mod_(d, m)))), d));
	assert(eq_(temp_102_0, temp_102_1)) by {
		lemma_mul_assoc(mul_(a, d), mod_(d, m), d);
	}
	let temp_103_0 = (mul_((sub_(b, c)), (mul_(a, b))));
	let temp_103_1 = (sub_((mul_(b, (mul_(a, b)))), (mul_(c, (mul_(a, b))))));
	assert(eq_(temp_103_0, temp_103_1)) by {
		lemma_mul_dist(mul_(a, b), b, c);
	}
	let temp_104_0 = (sub_((mul_(a, b)), (mul_((mod_(c, m)), b))));
	let temp_104_1 = (sub_((mul_(a, b)), (mul_((mod_((sub_(c, (mul_((mul_((sub_(a, a)), (mul_(d, a)))), m)))), m)), b))));
	assert(eq_(temp_104_0, temp_104_1)) by {
		lemma_eq_ref(mul_(a, b));
		cong_mul_(mod_(c, m), b, mod_(sub_(c, mul_(mul_(sub_(a, a), mul_(d, a)), m)), m), b);
		lemma_eq_ref(b);
		lemma_mod_mul_vanish(c, mul_(sub_(a, a), mul_(d, a)), m);
		cong_sub_(mul_(a, b), mul_(mod_(c, m), b), mul_(a, b), mul_(mod_(sub_(c, mul_(mul_(sub_(a, a), mul_(d, a)), m)), m), b));
	}
	let temp_105_0 = (mul_((sub_(as_elem(85), d)), (sub_((mod_(b, m)), d))));
	let temp_105_1 = (mul_((sub_((mod_(b, m)), d)), (sub_(as_elem(85), d))));
	assert(eq_(temp_105_0, temp_105_1)) by {
		lemma_mul_comm(sub_(as_elem(85), d), sub_(mod_(b, m), d));
	}
	let temp_106_0 = (mul_(c, (mul_(c, a))));
	let temp_106_1 = (mul_((mul_(c, c)), a));
	assert(eq_(temp_106_0, temp_106_1)) by {
		lemma_mul_assoc(c, c, a);
	}
	let temp_107_0 = (mul_((mod_((mul_(a, d)), m)), c));
	let temp_107_1 = (mul_((mod_((mul_(d, a)), m)), c));
	assert(eq_(temp_107_0, temp_107_1)) by {
		lemma_mul_comm(a, d);
		cong_mul_(mod_(mul_(a, d), m), c, mod_(mul_(d, a), m), c);
		cong_mod_(mul_(a, d), m, mul_(d, a), m);
		lemma_eq_ref(c);
		lemma_eq_ref(m);
	}
	let temp_108_0 = (mul_((sub_(c, c)), (mul_(b, b))));
	let temp_108_1 = (sub_((mul_(c, (mul_(b, b)))), (mul_(c, (mul_(b, b))))));
	assert(eq_(temp_108_0, temp_108_1)) by {
		lemma_mul_dist(mul_(b, b), c, c);
	}
	let temp_109_0 = (mod_((mul_((mul_(a, (mod_(d, m)))), (mul_(b, a)))), m));
	let temp_109_1 = (mod_((mul_(a, (mul_((mod_(d, m)), (mul_(b, a)))))), m));
	assert(eq_(temp_109_0, temp_109_1)) by {
		lemma_mul_assoc(a, mod_(d, m), mul_(b, a));
		cong_mod_(mul_(mul_(a, mod_(d, m)), mul_(b, a)), m, mul_(a, mul_(mod_(d, m), mul_(b, a))), m);
		lemma_eq_sym(mul_(a, mul_(mod_(d, m), mul_(b, a))), mul_(mul_(a, mod_(d, m)), mul_(b, a)));
		lemma_eq_ref(m);
	}

}

} // verus!