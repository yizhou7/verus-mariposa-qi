use builtin_macros::*;
// use builtin::*;
mod nl_basics;
use crate::nl_basics::*;
verus! {

pub proof fn free_0(a: Elem, b: Elem, c: Elem, d: Elem, m: Elem)
{
	let temp_0_0 = (mul_((add_(b, c)), (mul_(a, (mod_(b, m))))));
	let temp_0_1 = (mul_((add_(c, b)), (mul_(a, (mod_(b, m))))));
	assert(eq_(temp_0_0, temp_0_1)) by {
		lemma_add_comm(b, c);
		cong_mul_(add_(b, c), mul_(a, mod_(b, m)), add_(c, b), mul_(a, mod_(b, m)));
		lemma_eq_ref(mul_(a, mod_(b, m)));
	}
	let temp_1_0 = (mul_((mul_((mod_(a, m)), (mod_(a, m)))), (mul_((mod_(d, m)), b))));
	let temp_1_1 = (mul_((mod_(a, m)), (mul_((mod_(a, m)), (mul_((mod_(d, m)), b))))));
	assert(eq_(temp_1_0, temp_1_1)) by {
		lemma_mul_assoc(mod_(a, m), mod_(a, m), mul_(mod_(d, m), b));
		lemma_eq_sym(temp_1_1, temp_1_0);
	}
	let temp_2_0 = (mul_((mul_(c, d)), (sub_(as_elem(87), (mod_(b, m))))));
	let temp_2_1 = (mul_((mul_(c, d)), (sub_(as_elem(87), (mod_((add_(b, (mul_((mul_((mul_(d, b)), (sub_(a, c)))), m)))), m))))));
	assert(eq_(temp_2_0, temp_2_1)) by {
		lemma_eq_ref(as_elem(87));
		lemma_mod_mul_vanish(b, mul_(mul_(d, b), sub_(a, c)), m);
		cong_mul_(mul_(c, d), sub_(as_elem(87), mod_(b, m)), mul_(c, d), sub_(as_elem(87), mod_(add_(b, mul_(mul_(mul_(d, b), sub_(a, c)), m)), m)));
		cong_sub_(as_elem(87), mod_(b, m), as_elem(87), mod_(add_(b, mul_(mul_(mul_(d, b), sub_(a, c)), m)), m));
		lemma_eq_ref(mul_(c, d));
	}
	let temp_3_0 = (mul_((add_((mod_(c, m)), b)), (add_(c, d))));
	let temp_3_1 = (mul_((add_(c, d)), (add_((mod_(c, m)), b))));
	assert(eq_(temp_3_0, temp_3_1)) by {
		lemma_mul_comm(add_(mod_(c, m), b), add_(c, d));
	}
	let temp_4_0 = (mul_((mul_(c, b)), (mul_(d, d))));
	let temp_4_1 = (mul_((mul_(d, d)), (mul_(c, b))));
	assert(eq_(temp_4_0, temp_4_1)) by {
		lemma_mul_comm(mul_(c, b), mul_(d, d));
	}
	let temp_5_0 = (sub_((mul_(c, b)), (sub_(c, c))));
	let temp_5_1 = (sub_((mul_(b, c)), (sub_(c, c))));
	assert(eq_(temp_5_0, temp_5_1)) by {
		cong_sub_(mul_(c, b), sub_(c, c), mul_(b, c), sub_(c, c));
		lemma_mul_comm(c, b);
		lemma_eq_ref(sub_(c, c));
	}
	let temp_6_0 = (mod_((mul_((mul_(c, a)), (mul_(b, a)))), m));
	let temp_6_1 = (mod_((mul_((mul_(b, a)), (mul_(c, a)))), m));
	assert(eq_(temp_6_0, temp_6_1)) by {
		lemma_mul_comm(mul_(c, a), mul_(b, a));
		cong_mod_(mul_(mul_(c, a), mul_(b, a)), m, mul_(mul_(b, a), mul_(c, a)), m);
		lemma_eq_ref(m);
	}
	let temp_7_0 = (mul_((sub_(a, b)), (sub_(d, c))));
	let temp_7_1 = (sub_((mul_(a, (sub_(d, c)))), (mul_(b, (sub_(d, c))))));
	assert(eq_(temp_7_0, temp_7_1)) by {
		lemma_mul_dist(sub_(d, c), a, b);
	}
	let temp_8_0 = (mul_((mul_(d, (mod_(a, m)))), (mul_(d, b))));
	let temp_8_1 = (mul_((mul_(d, (mod_((add_(a, (mul_((mul_((mul_(b, d)), (add_(a, c)))), m)))), m)))), (mul_(d, b))));
	assert(eq_(temp_8_0, temp_8_1)) by {
		lemma_mod_mul_vanish(a, mul_(mul_(b, d), add_(a, c)), m);
		cong_mul_(mul_(d, mod_(a, m)), mul_(d, b), mul_(d, mod_(add_(a, mul_(mul_(mul_(b, d), add_(a, c)), m)), m)), mul_(d, b));
		lemma_eq_ref(d);
		lemma_eq_ref(mul_(d, b));
		cong_mul_(d, mod_(a, m), d, mod_(add_(a, mul_(mul_(mul_(b, d), add_(a, c)), m)), m));
	}
	let temp_9_0 = (mul_((mul_(c, c)), (mul_(d, d))));
	let temp_9_1 = (mul_(c, (mul_(c, (mul_(d, d))))));
	assert(eq_(temp_9_0, temp_9_1)) by {
		lemma_eq_sym(temp_9_1, temp_9_0);
		lemma_mul_assoc(c, c, mul_(d, d));
	}
	let temp_10_0 = (mul_((mul_(c, b)), (mul_(a, a))));
	let temp_10_1 = (mul_(c, (mul_(b, (mul_(a, a))))));
	assert(eq_(temp_10_0, temp_10_1)) by {
		lemma_eq_sym(temp_10_1, temp_10_0);
		lemma_mul_assoc(c, b, mul_(a, a));
	}
	let temp_11_0 = (mul_((mul_(as_elem(72), c)), (mul_(d, b))));
	let temp_11_1 = (mul_((mul_(c, as_elem(72))), (mul_(d, b))));
	assert(eq_(temp_11_0, temp_11_1)) by {
		lemma_mul_comm(as_elem(72), c);
		cong_mul_(mul_(as_elem(72), c), mul_(d, b), mul_(c, as_elem(72)), mul_(d, b));
		lemma_eq_ref(mul_(d, b));
	}
	let temp_12_0 = (mul_((add_(d, c)), (mul_(c, c))));
	let temp_12_1 = (mul_((mul_((add_(d, c)), c)), c));
	assert(eq_(temp_12_0, temp_12_1)) by {
		lemma_mul_assoc(add_(d, c), c, c);
	}
	let temp_13_0 = (mul_((mul_(b, a)), (mul_(a, a))));
	let temp_13_1 = (mul_((mul_(a, b)), (mul_(a, a))));
	assert(eq_(temp_13_0, temp_13_1)) by {
		cong_mul_(mul_(b, a), mul_(a, a), mul_(a, b), mul_(a, a));
		lemma_mul_comm(b, a);
		lemma_mul_comm(a, a);
	}
	let temp_14_0 = (mul_((mul_(b, b)), (mul_(c, d))));
	let temp_14_1 = (mul_((mul_((mul_(b, b)), c)), d));
	assert(eq_(temp_14_0, temp_14_1)) by {
		lemma_mul_assoc(mul_(b, b), c, d);
	}
	let temp_15_0 = (mul_((mul_(b, a)), (mul_(d, c))));
	let temp_15_1 = (mul_(b, (mul_(a, (mul_(d, c))))));
	assert(eq_(temp_15_0, temp_15_1)) by {
		lemma_eq_sym(temp_15_1, temp_15_0);
		lemma_mul_assoc(b, a, mul_(d, c));
	}
	let temp_16_0 = (mul_((sub_(d, d)), (mul_(a, a))));
	let temp_16_1 = (mul_((sub_(d, d)), (mul_(a, a))));
	assert(eq_(temp_16_0, temp_16_1)) by {
		lemma_eq_ref(temp_16_0);
	}
	let temp_17_0 = (mul_((mul_(a, b)), (mul_(a, c))));
	let temp_17_1 = (mul_((mul_(b, a)), (mul_(a, c))));
	assert(eq_(temp_17_0, temp_17_1)) by {
		cong_mul_(mul_(a, b), mul_(a, c), mul_(b, a), mul_(a, c));
		lemma_mul_comm(a, b);
		lemma_eq_ref(mul_(a, c));
	}
	let temp_18_0 = (mul_((mul_(b, d)), (mul_(c, a))));
	let temp_18_1 = (mul_((mul_(b, d)), (mul_(a, c))));
	assert(eq_(temp_18_0, temp_18_1)) by {
		cong_mul_(mul_(b, d), mul_(c, a), mul_(b, d), mul_(a, c));
		lemma_mul_comm(c, a);
		lemma_eq_ref(mul_(b, d));
	}
	let temp_19_0 = (add_((add_(a, (mod_(c, m)))), (mul_(c, b))));
	let temp_19_1 = (add_((add_(a, (mod_((add_((mul_((sub_((sub_(c, b)), (sub_(a, b)))), m)), c)), m)))), (mul_(c, b))));
	assert(eq_(temp_19_0, temp_19_1)) by {
		lemma_mod_mul_vanish(c, sub_(sub_(c, b), sub_(a, b)), m);
		cong_add_(add_(a, mod_(c, m)), mul_(c, b), add_(a, mod_(add_(mul_(sub_(sub_(c, b), sub_(a, b)), m), c), m)), mul_(c, b));
		lemma_eq_ref(a);
		cong_add_(a, mod_(c, m), a, mod_(add_(mul_(sub_(sub_(c, b), sub_(a, b)), m), c), m));
		lemma_eq_ref(mul_(c, b));
	}
	let temp_20_0 = (mul_((mod_((mul_(c, d)), m)), (mul_(c, a))));
	let temp_20_1 = (mul_((mul_((mod_((mul_(c, d)), m)), c)), a));
	assert(eq_(temp_20_0, temp_20_1)) by {
		lemma_mul_assoc(mod_(mul_(c, d), m), c, a);
	}
	let temp_21_0 = (mod_((mul_((mul_(b, a)), (sub_(b, c)))), m));
	let temp_21_1 = (mod_((mul_(b, (mul_(a, (sub_(b, c)))))), m));
	assert(eq_(temp_21_0, temp_21_1)) by {
		lemma_mul_assoc(b, a, sub_(b, c));
		cong_mod_(mul_(mul_(b, a), sub_(b, c)), m, mul_(b, mul_(a, sub_(b, c))), m);
		lemma_eq_sym(mul_(b, mul_(a, sub_(b, c))), mul_(mul_(b, a), sub_(b, c)));
		lemma_eq_ref(m);
	}
	let temp_22_0 = (mul_((add_(as_elem(52), d)), (mul_(d, b))));
	let temp_22_1 = (mul_((add_(d, as_elem(52))), (mul_(d, b))));
	assert(eq_(temp_22_0, temp_22_1)) by {
		lemma_add_comm(as_elem(52), d);
		cong_mul_(add_(as_elem(52), d), mul_(d, b), add_(d, as_elem(52)), mul_(d, b));
		lemma_eq_ref(mul_(d, b));
	}
	let temp_23_0 = (mul_((mul_(d, c)), (mul_(b, b))));
	let temp_23_1 = (mul_((mul_(c, d)), (mul_(b, b))));
	assert(eq_(temp_23_0, temp_23_1)) by {
		cong_mul_(mul_(d, c), mul_(b, b), mul_(c, d), mul_(b, b));
		lemma_mul_comm(d, c);
		lemma_mul_comm(b, b);
	}
	let temp_24_0 = (mul_((add_((mod_(b, m)), c)), (mul_(b, b))));
	let temp_24_1 = (add_((mul_((mod_(b, m)), (mul_(b, b)))), (mul_(c, (mul_(b, b))))));
	assert(eq_(temp_24_0, temp_24_1)) by {
		lemma_mul_dist(mod_(b, m), c, mul_(b, b));
	}
	let temp_25_0 = (sub_((mod_((mul_(b, c)), m)), (mul_(b, b))));
	let temp_25_1 = (sub_((mod_((mul_(c, b)), m)), (mul_(b, b))));
	assert(eq_(temp_25_0, temp_25_1)) by {
		lemma_mul_comm(b, c);
		lemma_mul_comm(b, b);
		cong_sub_(mod_(mul_(b, c), m), mul_(b, b), mod_(mul_(c, b), m), mul_(b, b));
		cong_mod_(mul_(b, c), m, mul_(c, b), m);
		lemma_eq_ref(m);
	}
	let temp_26_0 = (mul_((add_(b, d)), (mul_(c, a))));
	let temp_26_1 = (mul_((add_(d, b)), (mul_(c, a))));
	assert(eq_(temp_26_0, temp_26_1)) by {
		lemma_add_comm(b, d);
		cong_mul_(add_(b, d), mul_(c, a), add_(d, b), mul_(c, a));
		lemma_eq_ref(mul_(c, a));
	}
	let temp_27_0 = (mul_((mul_(b, b)), (mod_((mul_(a, a)), m))));
	let temp_27_1 = (mul_(b, (mul_(b, (mod_((mul_(a, a)), m))))));
	assert(eq_(temp_27_0, temp_27_1)) by {
		lemma_eq_sym(temp_27_1, temp_27_0);
		lemma_mul_assoc(b, b, mod_(mul_(a, a), m));
	}
	let temp_28_0 = (add_((mul_(c, d)), (mul_(c, a))));
	let temp_28_1 = (mul_(c, (add_(d, a))));
	assert(eq_(temp_28_0, temp_28_1)) by {
		lemma_eq_sym(temp_28_1, temp_28_0);
		lemma_mul_dist(c, d, a);
	}
	let temp_29_0 = (mul_((sub_(a, c)), (mul_(b, b))));
	let temp_29_1 = (sub_((mul_(a, (mul_(b, b)))), (mul_(c, (mul_(b, b))))));
	assert(eq_(temp_29_0, temp_29_1)) by {
		lemma_mul_dist(mul_(b, b), a, c);
	}
	let temp_30_0 = (add_((mul_(c, a)), (mul_(b, c))));
	let temp_30_1 = (add_((mul_(a, c)), (mul_(b, c))));
	assert(eq_(temp_30_0, temp_30_1)) by {
		cong_add_(mul_(c, a), mul_(b, c), mul_(a, c), mul_(b, c));
		lemma_mul_comm(c, a);
		lemma_eq_ref(mul_(b, c));
	}
	let temp_31_0 = (mod_((add_((mul_(d, (mod_(c, m)))), (mul_(a, b)))), m));
	let temp_31_1 = (mod_((add_((mul_(d, (mod_(c, m)))), (mul_(b, a)))), m));
	assert(eq_(temp_31_0, temp_31_1)) by {
		lemma_mul_comm(a, b);
		cong_mod_(add_(mul_(d, mod_(c, m)), mul_(a, b)), m, add_(mul_(d, mod_(c, m)), mul_(b, a)), m);
		lemma_eq_ref(m);
		lemma_eq_ref(mul_(d, mod_(c, m)));
		cong_add_(mul_(d, mod_(c, m)), mul_(a, b), mul_(d, mod_(c, m)), mul_(b, a));
	}
	let temp_32_0 = (sub_((mul_(c, a)), (mul_(b, a))));
	let temp_32_1 = (sub_((mul_(c, a)), (mul_(a, b))));
	assert(eq_(temp_32_0, temp_32_1)) by {
		cong_sub_(mul_(c, a), mul_(b, a), mul_(c, a), mul_(a, b));
		lemma_mul_comm(b, a);
		lemma_eq_ref(mul_(c, a));
	}
	let temp_33_0 = (mul_((mul_(d, b)), (mul_(b, b))));
	let temp_33_1 = (mul_((mul_(d, b)), (mul_(b, b))));
	assert(eq_(temp_33_0, temp_33_1)) by {
		lemma_eq_ref(temp_33_0);
	}
	let temp_34_0 = (mul_((mod_((mul_(a, a)), m)), (mul_(c, a))));
	let temp_34_1 = (mul_((mod_((mul_(a, a)), m)), (mul_(a, c))));
	assert(eq_(temp_34_0, temp_34_1)) by {
		cong_mul_(mod_(mul_(a, a), m), mul_(c, a), mod_(mul_(a, a), m), mul_(a, c));
		lemma_mul_comm(c, a);
		lemma_eq_ref(mod_(mul_(a, a), m));
	}
	let temp_35_0 = (mod_((sub_((mod_((mul_(d, c)), m)), (mul_(c, b)))), m));
	let temp_35_1 = (mod_((sub_((mod_((mul_(d, c)), m)), (mod_((mul_(c, b)), m)))), m));
	assert(eq_(temp_35_0, temp_35_1)) by {
		lemma_mod_sub_noop(mod_(mul_(d, c), m), mul_(c, b), m);
	}
	let temp_36_0 = (add_((mul_(c, b)), (mul_(a, b))));
	let temp_36_1 = (add_((mul_(c, b)), (mul_(b, a))));
	assert(eq_(temp_36_0, temp_36_1)) by {
		cong_add_(mul_(c, b), mul_(a, b), mul_(c, b), mul_(b, a));
		lemma_mul_comm(a, b);
		lemma_eq_ref(mul_(c, b));
	}
	let temp_37_0 = (mul_((mul_(b, a)), (mul_(a, b))));
	let temp_37_1 = (mul_(b, (mul_(a, (mul_(a, b))))));
	assert(eq_(temp_37_0, temp_37_1)) by {
		lemma_eq_sym(temp_37_1, temp_37_0);
		lemma_mul_assoc(b, a, mul_(a, b));
	}
	let temp_38_0 = (mul_((mul_(d, a)), (add_(d, a))));
	let temp_38_1 = (mul_(d, (mul_(a, (add_(d, a))))));
	assert(eq_(temp_38_0, temp_38_1)) by {
		lemma_eq_sym(temp_38_1, temp_38_0);
		lemma_mul_assoc(d, a, add_(d, a));
	}
	let temp_39_0 = (mul_((sub_(b, a)), (mul_(c, d))));
	let temp_39_1 = (mul_((mul_((sub_(b, a)), c)), d));
	assert(eq_(temp_39_0, temp_39_1)) by {
		lemma_mul_assoc(sub_(b, a), c, d);
	}
	let temp_40_0 = (mul_(c, (mul_(d, c))));
	let temp_40_1 = (mul_((mul_(c, d)), c));
	assert(eq_(temp_40_0, temp_40_1)) by {
		lemma_mul_assoc(c, d, c);
	}
	let temp_41_0 = (mod_((mul_((mul_(b, c)), (add_(c, c)))), m));
	let temp_41_1 = (mod_((add_((mul_((mul_(b, c)), c)), (mul_((mul_(b, c)), c)))), m));
	assert(eq_(temp_41_0, temp_41_1)) by {
		lemma_mul_dist(mul_(b, c), c, c);
		cong_mod_(mul_(mul_(b, c), add_(c, c)), m, add_(mul_(mul_(b, c), c), mul_(mul_(b, c), c)), m);
		lemma_eq_ref(m);
	}
	let temp_42_0 = (mod_((mul_((add_(a, c)), (mul_(b, b)))), m));
	let temp_42_1 = (mod_((sub_((mul_((add_(a, c)), (mul_(b, b)))), (mul_((mod_((add_((mul_(d, a)), (mul_(d, b)))), m)), m)))), m));
	assert(eq_(temp_42_0, temp_42_1)) by {
		lemma_mod_mul_vanish(mul_(add_(a, c), mul_(b, b)), mod_(add_(mul_(d, a), mul_(d, b)), m), m);
	}
	let temp_43_0 = (mul_((mul_(d, (mod_(b, m)))), (sub_((mod_(a, m)), (mod_(d, m))))));
	let temp_43_1 = (mul_((mul_((mod_(b, m)), d)), (sub_((mod_(a, m)), (mod_(d, m))))));
	assert(eq_(temp_43_0, temp_43_1)) by {
		lemma_mul_comm(d, mod_(b, m));
		cong_mul_(mul_(d, mod_(b, m)), sub_(mod_(a, m), mod_(d, m)), mul_(mod_(b, m), d), sub_(mod_(a, m), mod_(d, m)));
		lemma_eq_ref(sub_(mod_(a, m), mod_(d, m)));
	}
	let temp_44_0 = (mul_((mul_(b, c)), (mul_(a, b))));
	let temp_44_1 = (mul_((mul_((mul_(b, c)), a)), b));
	assert(eq_(temp_44_0, temp_44_1)) by {
		lemma_mul_assoc(mul_(b, c), a, b);
	}
	let temp_45_0 = (mul_((mul_(a, d)), (mul_(d, b))));
	let temp_45_1 = (mul_((mul_((mul_(a, d)), d)), b));
	assert(eq_(temp_45_0, temp_45_1)) by {
		lemma_mul_assoc(mul_(a, d), d, b);
	}
	let temp_46_0 = (mod_((mul_((mul_(b, c)), (mul_(b, c)))), m));
	let temp_46_1 = (mod_((mul_((mul_(c, b)), (mul_(b, c)))), m));
	assert(eq_(temp_46_0, temp_46_1)) by {
		cong_mod_(mul_(mul_(b, c), mul_(b, c)), m, mul_(mul_(c, b), mul_(b, c)), m);
		lemma_mul_comm(b, c);
		lemma_mul_comm(c, b);
		lemma_eq_ref(m);
		cong_mul_(mul_(b, c), mul_(b, c), mul_(c, b), mul_(b, c));
		lemma_eq_trans(mul_(b, c), mul_(c, b), mul_(b, c));
	}
	let temp_47_0 = (mul_((mul_(b, d)), (mul_(b, c))));
	let temp_47_1 = (mul_((mul_(b, d)), (mul_(c, b))));
	assert(eq_(temp_47_0, temp_47_1)) by {
		cong_mul_(mul_(b, d), mul_(b, c), mul_(b, d), mul_(c, b));
		lemma_mul_comm(b, c);
		lemma_eq_ref(mul_(b, d));
	}
	let temp_48_0 = (mod_((mul_((sub_(c, d)), (mul_(b, c)))), m));
	let temp_48_1 = (mod_((mul_((sub_(c, d)), (mul_(c, b)))), m));
	assert(eq_(temp_48_0, temp_48_1)) by {
		lemma_mul_comm(b, c);
		cong_mod_(mul_(sub_(c, d), mul_(b, c)), m, mul_(sub_(c, d), mul_(c, b)), m);
		cong_mul_(sub_(c, d), mul_(b, c), sub_(c, d), mul_(c, b));
		lemma_eq_ref(m);
		lemma_eq_ref(sub_(c, d));
	}
	let temp_49_0 = (mul_((mul_(d, a)), (mul_(b, b))));
	let temp_49_1 = (mul_(d, (mul_(a, (mul_(b, b))))));
	assert(eq_(temp_49_0, temp_49_1)) by {
		lemma_eq_sym(temp_49_1, temp_49_0);
		lemma_mul_assoc(d, a, mul_(b, b));
	}
	let temp_50_0 = (sub_((add_(b, (mod_(b, m)))), (mul_(b, d))));
	let temp_50_1 = (sub_((add_((mod_(b, m)), b)), (mul_(b, d))));
	assert(eq_(temp_50_0, temp_50_1)) by {
		lemma_add_comm(b, mod_(b, m));
		cong_sub_(add_(b, mod_(b, m)), mul_(b, d), add_(mod_(b, m), b), mul_(b, d));
		lemma_eq_ref(mul_(b, d));
	}
	let temp_51_0 = (sub_((mul_(c, as_elem(86))), (mul_(b, c))));
	let temp_51_1 = (sub_((mul_(c, as_elem(86))), (mul_(c, b))));
	assert(eq_(temp_51_0, temp_51_1)) by {
		cong_sub_(mul_(c, as_elem(86)), mul_(b, c), mul_(c, as_elem(86)), mul_(c, b));
		lemma_mul_comm(b, c);
		lemma_eq_ref(mul_(c, as_elem(86)));
	}
	let temp_52_0 = (mul_((mod_((mul_(b, a)), m)), (mul_(a, b))));
	let temp_52_1 = (mul_((mod_((mul_(a, b)), m)), (mul_(a, b))));
	assert(eq_(temp_52_0, temp_52_1)) by {
		cong_mul_(mod_(mul_(b, a), m), mul_(a, b), mod_(mul_(a, b), m), mul_(a, b));
		lemma_mul_comm(b, a);
		lemma_eq_ref(mul_(a, b));
		cong_mod_(mul_(b, a), m, mul_(a, b), m);
		lemma_eq_ref(m);
	}
	let temp_53_0 = (mul_((mul_(d, b)), (sub_(b, (mod_(b, m))))));
	let temp_53_1 = (mul_((mul_(d, b)), (sub_(b, (mod_((add_(b, (mul_((mul_((add_(c, d)), (mul_(c, b)))), m)))), m))))));
	assert(eq_(temp_53_0, temp_53_1)) by {
		lemma_mod_mul_vanish(b, mul_(add_(c, d), mul_(c, b)), m);
		cong_mul_(mul_(d, b), sub_(b, mod_(b, m)), mul_(d, b), sub_(b, mod_(add_(b, mul_(mul_(add_(c, d), mul_(c, b)), m)), m)));
		cong_sub_(b, mod_(b, m), b, mod_(add_(b, mul_(mul_(add_(c, d), mul_(c, b)), m)), m));
		lemma_eq_ref(mul_(d, b));
		lemma_eq_ref(b);
	}
	let temp_54_0 = (sub_((mul_(b, d)), (mul_(a, b))));
	let temp_54_1 = (sub_((mul_(d, b)), (mul_(a, b))));
	assert(eq_(temp_54_0, temp_54_1)) by {
		cong_sub_(mul_(b, d), mul_(a, b), mul_(d, b), mul_(a, b));
		lemma_mul_comm(b, d);
		lemma_eq_ref(mul_(a, b));
	}
	let temp_55_0 = (mul_((mul_(d, b)), (add_(c, a))));
	let temp_55_1 = (add_((mul_((mul_(d, b)), c)), (mul_((mul_(d, b)), a))));
	assert(eq_(temp_55_0, temp_55_1)) by {
		lemma_mul_dist(mul_(d, b), c, a);
	}
	let temp_56_0 = (mul_((mul_(b, b)), (mul_(d, (mod_(a, m))))));
	let temp_56_1 = (mul_((mul_(b, b)), (mul_(d, (mod_((add_(a, (mul_((mul_((mul_(d, d)), (mul_((mod_(a, m)), b)))), m)))), m))))));
	assert(eq_(temp_56_0, temp_56_1)) by {
		lemma_mul_comm(b, b);
		lemma_mod_mul_vanish(a, mul_(mul_(d, d), mul_(mod_(a, m), b)), m);
		cong_mul_(mul_(b, b), mul_(d, mod_(a, m)), mul_(b, b), mul_(d, mod_(add_(a, mul_(mul_(mul_(d, d), mul_(mod_(a, m), b)), m)), m)));
		lemma_eq_ref(d);
		cong_mul_(d, mod_(a, m), d, mod_(add_(a, mul_(mul_(mul_(d, d), mul_(mod_(a, m), b)), m)), m));
	}
	let temp_57_0 = (mul_((mul_(b, b)), (mod_((mul_(c, c)), m))));
	let temp_57_1 = (mul_((mul_(b, b)), (mod_((add_((mul_(c, c)), (mul_((mul_((sub_(d, c)), d)), m)))), m))));
	assert(eq_(temp_57_0, temp_57_1)) by {
		lemma_mul_comm(b, b);
		lemma_mod_mul_vanish(mul_(c, c), mul_(sub_(d, c), d), m);
		cong_mul_(mul_(b, b), mod_(mul_(c, c), m), mul_(b, b), mod_(add_(mul_(c, c), mul_(mul_(sub_(d, c), d), m)), m));
	}
	let temp_58_0 = (mul_((mul_((mod_(b, m)), c)), (mul_((mod_(c, m)), b))));
	let temp_58_1 = (mul_((mod_(b, m)), (mul_(c, (mul_((mod_(c, m)), b))))));
	assert(eq_(temp_58_0, temp_58_1)) by {
		lemma_mul_assoc(mod_(b, m), c, mul_(mod_(c, m), b));
		lemma_eq_sym(temp_58_1, temp_58_0);
	}
	let temp_59_0 = (mul_((mul_(a, b)), (mul_(d, b))));
	let temp_59_1 = (mul_((mul_((mul_(a, b)), d)), b));
	assert(eq_(temp_59_0, temp_59_1)) by {
		lemma_mul_assoc(mul_(a, b), d, b);
	}
	let temp_60_0 = (mul_((mul_(d, c)), (mul_(c, d))));
	let temp_60_1 = (mul_((mul_((mul_(d, c)), c)), d));
	assert(eq_(temp_60_0, temp_60_1)) by {
		lemma_mul_assoc(mul_(d, c), c, d);
	}
	let temp_61_0 = (mul_((mul_(d, as_elem(90))), (mul_(b, d))));
	let temp_61_1 = (mul_((mul_(as_elem(90), d)), (mul_(b, d))));
	assert(eq_(temp_61_0, temp_61_1)) by {
		cong_mul_(mul_(d, as_elem(90)), mul_(b, d), mul_(as_elem(90), d), mul_(b, d));
		lemma_mul_comm(d, as_elem(90));
		lemma_eq_ref(mul_(b, d));
	}
	let temp_62_0 = (mul_((sub_(a, b)), (mul_(b, b))));
	let temp_62_1 = (sub_((mul_(a, (mul_(b, b)))), (mul_(b, (mul_(b, b))))));
	assert(eq_(temp_62_0, temp_62_1)) by {
		lemma_mul_dist(mul_(b, b), a, b);
	}
	let temp_63_0 = (mod_((mul_((mul_(d, b)), (mul_(b, a)))), m));
	let temp_63_1 = (mod_((add_((mul_((add_((mul_(d, c)), (mul_(a, a)))), m)), (mul_((mul_(d, b)), (mul_(b, a)))))), m));
	assert(eq_(temp_63_0, temp_63_1)) by {
		lemma_mod_mul_vanish(mul_(mul_(d, b), mul_(b, a)), add_(mul_(d, c), mul_(a, a)), m);
	}
	let temp_64_0 = (mul_((mul_(d, a)), (mul_(c, b))));
	let temp_64_1 = (mul_((mul_(d, a)), (mul_(b, c))));
	assert(eq_(temp_64_0, temp_64_1)) by {
		cong_mul_(mul_(d, a), mul_(c, b), mul_(d, a), mul_(b, c));
		lemma_mul_comm(c, b);
		lemma_eq_ref(mul_(d, a));
	}
	let temp_65_0 = (mul_((mul_((mod_(c, m)), d)), (mul_(d, b))));
	let temp_65_1 = (mul_((mul_(d, (mod_(c, m)))), (mul_(d, b))));
	assert(eq_(temp_65_0, temp_65_1)) by {
		lemma_mul_comm(mod_(c, m), d);
		cong_mul_(mul_(mod_(c, m), d), mul_(d, b), mul_(d, mod_(c, m)), mul_(d, b));
		lemma_eq_ref(mul_(d, b));
	}
	let temp_66_0 = (mul_((mul_(b, d)), (mul_(b, b))));
	let temp_66_1 = (mul_((mul_((mul_(b, d)), b)), b));
	assert(eq_(temp_66_0, temp_66_1)) by {
		lemma_mul_assoc(mul_(b, d), b, b);
	}
	let temp_67_0 = (mul_((mul_(a, b)), (mul_(d, b))));
	let temp_67_1 = (mul_((mul_((mul_(a, b)), d)), b));
	assert(eq_(temp_67_0, temp_67_1)) by {
		lemma_mul_assoc(mul_(a, b), d, b);
	}
	let temp_68_0 = (add_((mul_(b, a)), (mul_(b, b))));
	let temp_68_1 = (add_((mul_(b, b)), (mul_(b, a))));
	assert(eq_(temp_68_0, temp_68_1)) by {
		lemma_add_comm(mul_(b, a), mul_(b, b));
	}
	let temp_69_0 = (mul_((mul_(d, d)), d));
	let temp_69_1 = (mul_((mul_(d, d)), d));
	assert(eq_(temp_69_0, temp_69_1)) by {
		lemma_eq_ref(temp_69_0);
	}
	let temp_70_0 = (mul_((mul_(c, d)), (mul_(b, c))));
	let temp_70_1 = (mul_((mul_(d, c)), (mul_(b, c))));
	assert(eq_(temp_70_0, temp_70_1)) by {
		cong_mul_(mul_(c, d), mul_(b, c), mul_(d, c), mul_(b, c));
		lemma_mul_comm(c, d);
		lemma_eq_ref(mul_(b, c));
	}
	let temp_71_0 = (mul_((mul_(b, b)), (mul_(c, as_elem(11)))));
	let temp_71_1 = (mul_((mul_((mul_(b, b)), c)), as_elem(11)));
	assert(eq_(temp_71_0, temp_71_1)) by {
		lemma_mul_assoc(mul_(b, b), c, as_elem(11));
	}
	let temp_72_0 = (sub_((mul_(a, c)), (sub_(c, a))));
	let temp_72_1 = (sub_((mul_(c, a)), (sub_(c, a))));
	assert(eq_(temp_72_0, temp_72_1)) by {
		cong_sub_(mul_(a, c), sub_(c, a), mul_(c, a), sub_(c, a));
		lemma_mul_comm(a, c);
		lemma_eq_ref(sub_(c, a));
	}
	let temp_73_0 = (mul_((mul_(as_elem(88), a)), (mul_(a, b))));
	let temp_73_1 = (mul_((mul_(as_elem(88), a)), (mul_(b, a))));
	assert(eq_(temp_73_0, temp_73_1)) by {
		cong_mul_(mul_(as_elem(88), a), mul_(a, b), mul_(as_elem(88), a), mul_(b, a));
		lemma_mul_comm(a, b);
		lemma_eq_ref(mul_(as_elem(88), a));
	}
	let temp_74_0 = (mul_((mul_((mod_(c, m)), b)), (mul_(d, a))));
	let temp_74_1 = (mul_((mul_((mod_((add_((mul_((sub_((mul_(a, b)), (mul_(b, a)))), m)), c)), m)), b)), (mul_(d, a))));
	assert(eq_(temp_74_0, temp_74_1)) by {
		lemma_mod_mul_vanish(c, sub_(mul_(a, b), mul_(b, a)), m);
		cong_mul_(mul_(mod_(c, m), b), mul_(d, a), mul_(mod_(add_(mul_(sub_(mul_(a, b), mul_(b, a)), m), c), m), b), mul_(d, a));
		lemma_eq_ref(b);
		cong_mul_(mod_(c, m), b, mod_(add_(mul_(sub_(mul_(a, b), mul_(b, a)), m), c), m), b);
		lemma_eq_ref(mul_(d, a));
	}
	let temp_75_0 = (mul_((mul_((mod_(b, m)), a)), (add_(d, a))));
	let temp_75_1 = (add_((mul_((mul_((mod_(b, m)), a)), d)), (mul_((mul_((mod_(b, m)), a)), a))));
	assert(eq_(temp_75_0, temp_75_1)) by {
		lemma_mul_dist(mul_(mod_(b, m), a), d, a);
	}
	let temp_76_0 = (mul_((sub_(d, c)), (mul_((mod_(as_elem(37), m)), a))));
	let temp_76_1 = (sub_((mul_(d, (mul_((mod_(as_elem(37), m)), a)))), (mul_(c, (mul_((mod_(as_elem(37), m)), a))))));
	assert(eq_(temp_76_0, temp_76_1)) by {
		lemma_mul_dist(mul_(mod_(as_elem(37), m), a), d, c);
	}
	let temp_77_0 = (add_((mul_(c, b)), (mul_(b, d))));
	let temp_77_1 = (add_((mul_(b, c)), (mul_(b, d))));
	assert(eq_(temp_77_0, temp_77_1)) by {
		cong_add_(mul_(c, b), mul_(b, d), mul_(b, c), mul_(b, d));
		lemma_mul_comm(c, b);
		lemma_eq_ref(mul_(b, d));
	}
	let temp_78_0 = (add_((add_(c, b)), (mul_(c, c))));
	let temp_78_1 = (add_((mul_(c, c)), (add_(c, b))));
	assert(eq_(temp_78_0, temp_78_1)) by {
		lemma_add_comm(add_(c, b), mul_(c, c));
	}
	let temp_79_0 = (mod_((mul_((mod_((sub_(d, c)), m)), (mul_(d, as_elem(79))))), m));
	let temp_79_1 = (mod_((mul_((mul_((mod_((sub_(d, c)), m)), d)), as_elem(79))), m));
	assert(eq_(temp_79_0, temp_79_1)) by {
		lemma_mul_assoc(mod_(sub_(d, c), m), d, as_elem(79));
		cong_mod_(mul_(mod_(sub_(d, c), m), mul_(d, as_elem(79))), m, mul_(mul_(mod_(sub_(d, c), m), d), as_elem(79)), m);
		lemma_eq_ref(m);
	}
	let temp_80_0 = (mul_((sub_(a, c)), (mul_(c, b))));
	let temp_80_1 = (mul_((mul_(c, b)), (sub_(a, c))));
	assert(eq_(temp_80_0, temp_80_1)) by {
		lemma_mul_comm(sub_(a, c), mul_(c, b));
	}
	let temp_81_0 = (mul_((mul_(a, d)), (mod_((add_(c, (mod_(b, m)))), m))));
	let temp_81_1 = (mul_((mul_(a, d)), (mod_((add_(c, b)), m))));
	assert(eq_(temp_81_0, temp_81_1)) by {
		lemma_mod_add_noop(c, b, m);
		cong_mul_(mul_(a, d), mod_(add_(c, mod_(b, m)), m), mul_(a, d), mod_(add_(c, b), m));
		lemma_eq_ref(mul_(a, d));
		lemma_eq_sym(mod_(add_(c, b), m), mod_(add_(c, mod_(b, m)), m));
	}
	let temp_82_0 = (sub_((mul_(c, b)), c));
	let temp_82_1 = (sub_((mul_(b, c)), c));
	assert(eq_(temp_82_0, temp_82_1)) by {
		cong_sub_(mul_(c, b), c, mul_(b, c), c);
		lemma_mul_comm(c, b);
		lemma_eq_ref(c);
	}
	let temp_83_0 = (add_((mul_(a, c)), (mod_((mul_((mod_(a, m)), a)), m))));
	let temp_83_1 = (add_((mul_(a, c)), (mod_((add_((mul_((add_((add_(a, (mod_(d, m)))), (mul_(b, a)))), m)), (mul_((mod_(a, m)), a)))), m))));
	assert(eq_(temp_83_0, temp_83_1)) by {
		lemma_mod_mul_vanish(mul_(mod_(a, m), a), add_(add_(a, mod_(d, m)), mul_(b, a)), m);
		cong_add_(mul_(a, c), mod_(mul_(mod_(a, m), a), m), mul_(a, c), mod_(add_(mul_(add_(add_(a, mod_(d, m)), mul_(b, a)), m), mul_(mod_(a, m), a)), m));
		lemma_eq_ref(mul_(a, c));
	}
	let temp_84_0 = (mul_((mul_(a, d)), (sub_(a, b))));
	let temp_84_1 = (mul_((mul_(d, a)), (sub_(a, b))));
	assert(eq_(temp_84_0, temp_84_1)) by {
		lemma_eq_ref(sub_(a, b));
		cong_mul_(mul_(a, d), sub_(a, b), mul_(d, a), sub_(a, b));
		lemma_mul_comm(a, d);
	}
	let temp_85_0 = (mul_((mul_(b, (mod_(d, m)))), (mul_(d, d))));
	let temp_85_1 = (mul_((mul_(b, (mod_((sub_(d, (mul_((mul_((mul_(b, a)), (mul_(b, d)))), m)))), m)))), (mul_(d, d))));
	assert(eq_(temp_85_0, temp_85_1)) by {
		lemma_mul_comm(d, d);
		lemma_mod_mul_vanish(d, mul_(mul_(b, a), mul_(b, d)), m);
		cong_mul_(mul_(b, mod_(d, m)), mul_(d, d), mul_(b, mod_(sub_(d, mul_(mul_(mul_(b, a), mul_(b, d)), m)), m)), mul_(d, d));
		lemma_eq_ref(b);
		cong_mul_(b, mod_(d, m), b, mod_(sub_(d, mul_(mul_(mul_(b, a), mul_(b, d)), m)), m));
	}
	let temp_86_0 = (mul_((mul_(b, b)), (mul_(d, c))));
	let temp_86_1 = (mul_(b, (mul_(b, (mul_(d, c))))));
	assert(eq_(temp_86_0, temp_86_1)) by {
		lemma_eq_sym(temp_86_1, temp_86_0);
		lemma_mul_assoc(b, b, mul_(d, c));
	}
	let temp_87_0 = (mul_((mul_(c, d)), (mul_(d, b))));
	let temp_87_1 = (mul_((mul_(d, b)), (mul_(c, d))));
	assert(eq_(temp_87_0, temp_87_1)) by {
		lemma_mul_comm(mul_(c, d), mul_(d, b));
	}
	let temp_88_0 = (add_((mul_(b, a)), (mul_(d, c))));
	let temp_88_1 = (add_((mul_(a, b)), (mul_(d, c))));
	assert(eq_(temp_88_0, temp_88_1)) by {
		cong_add_(mul_(b, a), mul_(d, c), mul_(a, b), mul_(d, c));
		lemma_mul_comm(b, a);
		lemma_eq_ref(mul_(d, c));
	}
	let temp_89_0 = (mul_((mul_(d, d)), (mul_(d, (mod_(as_elem(16), m))))));
	let temp_89_1 = (mul_((mul_(d, d)), (mul_(d, (mod_((add_((mul_((mul_((mul_((mod_(c, m)), b)), (mul_(d, a)))), m)), as_elem(16))), m))))));
	assert(eq_(temp_89_0, temp_89_1)) by {
		lemma_mul_comm(d, d);
		lemma_mod_mul_vanish(as_elem(16), mul_(mul_(mod_(c, m), b), mul_(d, a)), m);
		cong_mul_(mul_(d, d), mul_(d, mod_(as_elem(16), m)), mul_(d, d), mul_(d, mod_(add_(mul_(mul_(mul_(mod_(c, m), b), mul_(d, a)), m), as_elem(16)), m)));
		cong_mul_(d, mod_(as_elem(16), m), d, mod_(add_(mul_(mul_(mul_(mod_(c, m), b), mul_(d, a)), m), as_elem(16)), m));
		lemma_eq_ref(d);
	}
	let temp_90_0 = (mul_((mod_((mul_(c, c)), m)), (mul_((mod_(d, m)), b))));
	let temp_90_1 = (mul_((mul_((mod_((mul_(c, c)), m)), (mod_(d, m)))), b));
	assert(eq_(temp_90_0, temp_90_1)) by {
		lemma_mul_assoc(mod_(mul_(c, c), m), mod_(d, m), b);
	}
	let temp_91_0 = (mul_((mul_(a, b)), (mul_(c, c))));
	let temp_91_1 = (mul_(a, (mul_(b, (mul_(c, c))))));
	assert(eq_(temp_91_0, temp_91_1)) by {
		lemma_eq_sym(temp_91_1, temp_91_0);
		lemma_mul_assoc(a, b, mul_(c, c));
	}
	let temp_92_0 = (mul_((mul_(a, c)), (mul_(b, c))));
	let temp_92_1 = (mul_((mul_((mul_(a, c)), b)), c));
	assert(eq_(temp_92_0, temp_92_1)) by {
		lemma_mul_assoc(mul_(a, c), b, c);
	}
	let temp_93_0 = (sub_((mul_(a, a)), c));
	let temp_93_1 = (sub_((mul_(a, a)), c));
	assert(eq_(temp_93_0, temp_93_1)) by {
		lemma_eq_ref(temp_93_0);
	}
	let temp_94_0 = (mul_((mul_((mod_(a, m)), b)), (mul_(b, c))));
	let temp_94_1 = (mul_((mod_(a, m)), (mul_(b, (mul_(b, c))))));
	assert(eq_(temp_94_0, temp_94_1)) by {
		lemma_mul_assoc(mod_(a, m), b, mul_(b, c));
		lemma_eq_sym(temp_94_1, temp_94_0);
	}
	let temp_95_0 = (mul_((sub_(c, as_elem(49))), (mul_(a, b))));
	let temp_95_1 = (mul_((mul_((sub_(c, as_elem(49))), a)), b));
	assert(eq_(temp_95_0, temp_95_1)) by {
		lemma_mul_assoc(sub_(c, as_elem(49)), a, b);
	}
	let temp_96_0 = (mul_((mul_(d, c)), (mod_((mul_(a, b)), m))));
	let temp_96_1 = (mul_(d, (mul_(c, (mod_((mul_(a, b)), m))))));
	assert(eq_(temp_96_0, temp_96_1)) by {
		lemma_mul_assoc(d, c, mod_(mul_(a, b), m));
		lemma_eq_sym(temp_96_1, temp_96_0);
	}
	let temp_97_0 = (mod_((mul_((mul_(b, d)), (mul_(b, (mod_(a, m)))))), m));
	let temp_97_1 = (mod_((add_((mul_((mul_(b, d)), (mul_(b, (mod_(a, m)))))), (mul_((mul_((mul_(c, d)), (mul_(a, b)))), m)))), m));
	assert(eq_(temp_97_0, temp_97_1)) by {
		lemma_mod_mul_vanish(mul_(mul_(b, d), mul_(b, mod_(a, m))), mul_(mul_(c, d), mul_(a, b)), m);
	}
	let temp_98_0 = (mul_((mul_(b, d)), (mul_(a, a))));
	let temp_98_1 = (mul_(b, (mul_(d, (mul_(a, a))))));
	assert(eq_(temp_98_0, temp_98_1)) by {
		lemma_eq_sym(temp_98_1, temp_98_0);
		lemma_mul_assoc(b, d, mul_(a, a));
	}
	let temp_99_0 = (add_((mod_((mul_(c, d)), m)), (mul_(c, a))));
	let temp_99_1 = (add_((mod_((add_((mul_((mod_((sub_((mul_(as_elem(55), b)), (mul_(a, a)))), m)), m)), (mul_(c, d)))), m)), (mul_(c, a))));
	assert(eq_(temp_99_0, temp_99_1)) by {
		lemma_mod_mul_vanish(mul_(c, d), mod_(sub_(mul_(as_elem(55), b), mul_(a, a)), m), m);
		cong_add_(mod_(mul_(c, d), m), mul_(c, a), mod_(add_(mul_(mod_(sub_(mul_(as_elem(55), b), mul_(a, a)), m), m), mul_(c, d)), m), mul_(c, a));
		lemma_eq_ref(mul_(c, a));
	}
	let temp_100_0 = (mul_((mul_(a, b)), (mul_(b, d))));
	let temp_100_1 = (mul_((mul_((mul_(a, b)), b)), d));
	assert(eq_(temp_100_0, temp_100_1)) by {
		lemma_mul_assoc(mul_(a, b), b, d);
	}
	let temp_101_0 = (mul_((mul_(b, d)), (mod_((mul_(c, a)), m))));
	let temp_101_1 = (mul_((mul_(b, d)), (mod_((add_((mul_((mul_((mul_(c, b)), (mul_(a, a)))), m)), (mul_(c, a)))), m))));
	assert(eq_(temp_101_0, temp_101_1)) by {
		lemma_mod_mul_vanish(mul_(c, a), mul_(mul_(c, b), mul_(a, a)), m);
		cong_mul_(mul_(b, d), mod_(mul_(c, a), m), mul_(b, d), mod_(add_(mul_(mul_(mul_(c, b), mul_(a, a)), m), mul_(c, a)), m));
		lemma_eq_ref(mul_(b, d));
	}
	let temp_102_0 = (mul_((mul_(b, (mod_(d, m)))), (mod_((mul_(a, b)), m))));
	let temp_102_1 = (mul_((mul_(b, (mod_((sub_(d, (mul_((mul_((sub_(d, c)), (mul_(c, (mod_(a, m)))))), m)))), m)))), (mod_((mul_(a, b)), m))));
	assert(eq_(temp_102_0, temp_102_1)) by {
		cong_mul_(mul_(b, mod_(d, m)), mod_(mul_(a, b), m), mul_(b, mod_(sub_(d, mul_(mul_(sub_(d, c), mul_(c, mod_(a, m))), m)), m)), mod_(mul_(a, b), m));
		lemma_mod_mul_vanish(d, mul_(sub_(d, c), mul_(c, mod_(a, m))), m);
		lemma_eq_ref(b);
		cong_mul_(b, mod_(d, m), b, mod_(sub_(d, mul_(mul_(sub_(d, c), mul_(c, mod_(a, m))), m)), m));
		lemma_eq_ref(mod_(mul_(a, b), m));
	}
	let temp_103_0 = (add_((mul_(a, c)), (add_(a, b))));
	let temp_103_1 = (add_((mul_(a, c)), (add_(b, a))));
	assert(eq_(temp_103_0, temp_103_1)) by {
		cong_add_(mul_(a, c), add_(a, b), mul_(a, c), add_(b, a));
		lemma_add_comm(a, b);
		lemma_eq_ref(mul_(a, c));
	}
	let temp_104_0 = (mul_((mul_((mod_(b, m)), d)), (mul_(a, d))));
	let temp_104_1 = (mul_((mod_(b, m)), (mul_(d, (mul_(a, d))))));
	assert(eq_(temp_104_0, temp_104_1)) by {
		lemma_mul_assoc(mod_(b, m), d, mul_(a, d));
		lemma_eq_sym(temp_104_1, temp_104_0);
	}
	let temp_105_0 = (add_((mul_(c, d)), (mul_(a, a))));
	let temp_105_1 = (add_((mul_(c, d)), (mul_(a, a))));
	assert(eq_(temp_105_0, temp_105_1)) by {
		lemma_eq_ref(temp_105_0);
	}
	let temp_106_0 = (mul_((mul_(a, d)), (mul_(d, a))));
	let temp_106_1 = (mul_((mul_((mul_(a, d)), d)), a));
	assert(eq_(temp_106_0, temp_106_1)) by {
		lemma_mul_assoc(mul_(a, d), d, a);
	}
	let temp_107_0 = (sub_((mul_(a, b)), (mul_(d, d))));
	let temp_107_1 = (sub_((mul_(a, b)), (mul_(d, d))));
	assert(eq_(temp_107_0, temp_107_1)) by {
		lemma_eq_ref(temp_107_0);
	}
	let temp_108_0 = (mul_((mul_(d, b)), (mul_(c, c))));
	let temp_108_1 = (mul_(d, (mul_(b, (mul_(c, c))))));
	assert(eq_(temp_108_0, temp_108_1)) by {
		lemma_eq_sym(temp_108_1, temp_108_0);
		lemma_mul_assoc(d, b, mul_(c, c));
	}
	let temp_109_0 = (mul_((mul_(a, (mod_(a, m)))), b));
	let temp_109_1 = (mul_((mul_((mod_(a, m)), a)), b));
	assert(eq_(temp_109_0, temp_109_1)) by {
		cong_mul_(mul_(a, mod_(a, m)), b, mul_(mod_(a, m), a), b);
		lemma_mul_comm(a, mod_(a, m));
		lemma_eq_ref(b);
	}
	let temp_110_0 = (sub_((mul_(a, a)), (sub_(b, b))));
	let temp_110_1 = (sub_((mul_(a, a)), (sub_(b, b))));
	assert(eq_(temp_110_0, temp_110_1)) by {
		lemma_eq_ref(temp_110_0);
	}
	let temp_111_0 = (mod_((mul_((mul_(a, a)), (mul_((mod_(c, m)), d)))), m));
	let temp_111_1 = (mod_((mul_((mul_((mul_(a, a)), (mod_(c, m)))), d)), m));
	assert(eq_(temp_111_0, temp_111_1)) by {
		lemma_mul_assoc(mul_(a, a), mod_(c, m), d);
		cong_mod_(mul_(mul_(a, a), mul_(mod_(c, m), d)), m, mul_(mul_(mul_(a, a), mod_(c, m)), d), m);
		lemma_eq_ref(m);
	}
	let temp_112_0 = (mul_((add_((mod_(b, m)), b)), (mul_(d, c))));
	let temp_112_1 = (mul_((add_(b, (mod_(b, m)))), (mul_(d, c))));
	assert(eq_(temp_112_0, temp_112_1)) by {
		lemma_add_comm(mod_(b, m), b);
		cong_mul_(add_(mod_(b, m), b), mul_(d, c), add_(b, mod_(b, m)), mul_(d, c));
		lemma_eq_ref(mul_(d, c));
	}
	let temp_113_0 = (mul_((sub_(b, d)), (mul_(b, c))));
	let temp_113_1 = (mul_((mul_((sub_(b, d)), b)), c));
	assert(eq_(temp_113_0, temp_113_1)) by {
		lemma_mul_assoc(sub_(b, d), b, c);
	}
	let temp_114_0 = (add_((mod_((mul_(d, d)), m)), (mul_(d, (mod_(a, m))))));
	let temp_114_1 = (add_((mod_((mul_(d, d)), m)), (mul_(d, (mod_(a, m))))));
	assert(eq_(temp_114_0, temp_114_1)) by {
		lemma_eq_ref(temp_114_0);
	}
	let temp_115_0 = (mod_((mul_((mod_((mul_(b, c)), m)), (mul_(d, b)))), m));
	let temp_115_1 = (mod_((mul_((mul_((mod_((mul_(b, c)), m)), d)), b)), m));
	assert(eq_(temp_115_0, temp_115_1)) by {
		lemma_mul_assoc(mod_(mul_(b, c), m), d, b);
		cong_mod_(mul_(mod_(mul_(b, c), m), mul_(d, b)), m, mul_(mul_(mod_(mul_(b, c), m), d), b), m);
		lemma_eq_ref(m);
	}
	let temp_116_0 = (mul_((sub_(c, d)), (mul_(b, c))));
	let temp_116_1 = (mul_((mul_(b, c)), (sub_(c, d))));
	assert(eq_(temp_116_0, temp_116_1)) by {
		lemma_mul_comm(sub_(c, d), mul_(b, c));
	}
	let temp_117_0 = (mul_((mul_(c, a)), a));
	let temp_117_1 = (mul_((mul_(a, c)), a));
	assert(eq_(temp_117_0, temp_117_1)) by {
		cong_mul_(mul_(c, a), a, mul_(a, c), a);
		lemma_mul_comm(c, a);
		lemma_eq_ref(a);
	}
	let temp_118_0 = (mul_((sub_(d, d)), (mul_(b, a))));
	let temp_118_1 = (mul_((mul_((sub_(d, d)), b)), a));
	assert(eq_(temp_118_0, temp_118_1)) by {
		lemma_mul_assoc(sub_(d, d), b, a);
	}
	let temp_119_0 = (mul_((sub_(c, c)), (mul_(c, a))));
	let temp_119_1 = (mul_((mul_((sub_(c, c)), c)), a));
	assert(eq_(temp_119_0, temp_119_1)) by {
		lemma_mul_assoc(sub_(c, c), c, a);
	}
	let temp_120_0 = (mul_((mul_(as_elem(65), d)), (mul_(a, c))));
	let temp_120_1 = (mul_((mul_((mul_(as_elem(65), d)), a)), c));
	assert(eq_(temp_120_0, temp_120_1)) by {
		lemma_mul_assoc(mul_(as_elem(65), d), a, c);
	}
	let temp_121_0 = (mul_((mod_((mul_(a, c)), m)), (sub_(a, b))));
	let temp_121_1 = (mul_((mod_((mul_(c, a)), m)), (sub_(a, b))));
	assert(eq_(temp_121_0, temp_121_1)) by {
		cong_mod_(mul_(a, c), m, mul_(c, a), m);
		lemma_eq_ref(sub_(a, b));
		lemma_mul_comm(a, c);
		cong_mul_(mod_(mul_(a, c), m), sub_(a, b), mod_(mul_(c, a), m), sub_(a, b));
		lemma_eq_ref(m);
	}
	let temp_122_0 = (add_((mul_(a, (mod_(d, m)))), (mul_(a, d))));
	let temp_122_1 = (mul_(a, (add_((mod_(d, m)), d))));
	assert(eq_(temp_122_0, temp_122_1)) by {
		lemma_eq_sym(temp_122_1, temp_122_0);
		lemma_mul_dist(a, mod_(d, m), d);
	}
	let temp_123_0 = (mod_((mul_((mul_(d, c)), (mul_(d, d)))), m));
	let temp_123_1 = (mod_((sub_((mul_((mul_(d, c)), (mul_(d, d)))), (mul_((mul_((mul_((mod_(a, m)), d)), (sub_(b, a)))), m)))), m));
	assert(eq_(temp_123_0, temp_123_1)) by {
		lemma_mod_mul_vanish(mul_(mul_(d, c), mul_(d, d)), mul_(mul_(mod_(a, m), d), sub_(b, a)), m);
	}
	let temp_124_0 = (add_((sub_((mod_(c, m)), d)), (mul_(c, a))));
	let temp_124_1 = (add_((sub_((mod_(c, m)), d)), (mul_(a, c))));
	assert(eq_(temp_124_0, temp_124_1)) by {
		lemma_mul_comm(c, a);
		cong_add_(sub_(mod_(c, m), d), mul_(c, a), sub_(mod_(c, m), d), mul_(a, c));
		lemma_eq_ref(sub_(mod_(c, m), d));
	}
	let temp_125_0 = (mul_((mod_((mul_(b, c)), m)), (mul_(d, as_elem(69)))));
	let temp_125_1 = (mul_((mul_((mod_((mul_(b, c)), m)), d)), as_elem(69)));
	assert(eq_(temp_125_0, temp_125_1)) by {
		lemma_mul_assoc(mod_(mul_(b, c), m), d, as_elem(69));
	}
	let temp_126_0 = (mul_((mod_((mul_(c, b)), m)), (mul_(a, c))));
	let temp_126_1 = (mul_((mul_((mod_((mul_(c, b)), m)), a)), c));
	assert(eq_(temp_126_0, temp_126_1)) by {
		lemma_mul_assoc(mod_(mul_(c, b), m), a, c);
	}
	let temp_127_0 = (mod_((mul_((mod_((mul_(c, b)), m)), (sub_(c, c)))), m));
	let temp_127_1 = (mod_((mul_((mod_((add_((mul_(c, b)), (mul_((mul_((mul_(b, c)), (mul_(c, a)))), m)))), m)), (sub_(c, c)))), m));
	assert(eq_(temp_127_0, temp_127_1)) by {
		lemma_mod_mul_vanish(mul_(c, b), mul_(mul_(b, c), mul_(c, a)), m);
		cong_mod_(mul_(mod_(mul_(c, b), m), sub_(c, c)), m, mul_(mod_(add_(mul_(c, b), mul_(mul_(mul_(b, c), mul_(c, a)), m)), m), sub_(c, c)), m);
		lemma_eq_ref(m);
		lemma_eq_ref(sub_(c, c));
		cong_mul_(mod_(mul_(c, b), m), sub_(c, c), mod_(add_(mul_(c, b), mul_(mul_(mul_(b, c), mul_(c, a)), m)), m), sub_(c, c));
	}
	let temp_128_0 = (mul_((mul_(a, d)), (mul_(d, b))));
	let temp_128_1 = (mul_(a, (mul_(d, (mul_(d, b))))));
	assert(eq_(temp_128_0, temp_128_1)) by {
		lemma_eq_sym(temp_128_1, temp_128_0);
		lemma_mul_assoc(a, d, mul_(d, b));
	}
	let temp_129_0 = (mul_((mul_(b, a)), (add_(b, (mod_(b, m))))));
	let temp_129_1 = (mul_((mul_(a, b)), (add_(b, (mod_(b, m))))));
	assert(eq_(temp_129_0, temp_129_1)) by {
		cong_mul_(mul_(b, a), add_(b, mod_(b, m)), mul_(a, b), add_(b, mod_(b, m)));
		lemma_mul_comm(b, a);
		lemma_eq_ref(add_(b, mod_(b, m)));
	}
	let temp_130_0 = (mul_((mul_((mod_(c, m)), c)), (mul_(c, d))));
	let temp_130_1 = (mul_((mul_((mod_((add_((mul_((mul_((mul_(c, d)), (mul_(b, b)))), m)), c)), m)), c)), (mul_(c, d))));
	assert(eq_(temp_130_0, temp_130_1)) by {
		lemma_mod_mul_vanish(c, mul_(mul_(c, d), mul_(b, b)), m);
		cong_mul_(mul_(mod_(c, m), c), mul_(c, d), mul_(mod_(add_(mul_(mul_(mul_(c, d), mul_(b, b)), m), c), m), c), mul_(c, d));
		lemma_eq_ref(c);
		cong_mul_(mod_(c, m), c, mod_(add_(mul_(mul_(mul_(c, d), mul_(b, b)), m), c), m), c);
		lemma_eq_ref(mul_(c, d));
	}
	let temp_131_0 = (mul_((add_(a, a)), (mul_(a, c))));
	let temp_131_1 = (mul_((add_(a, a)), (mul_(a, c))));
	assert(eq_(temp_131_0, temp_131_1)) by {
		lemma_eq_ref(temp_131_0);
	}
	let temp_132_0 = (sub_((mul_(d, c)), (mul_(d, a))));
	let temp_132_1 = (sub_((mul_(c, d)), (mul_(d, a))));
	assert(eq_(temp_132_0, temp_132_1)) by {
		cong_sub_(mul_(d, c), mul_(d, a), mul_(c, d), mul_(d, a));
		lemma_mul_comm(d, c);
		lemma_eq_ref(mul_(d, a));
	}
	let temp_133_0 = (mul_((add_(b, a)), (mul_(d, d))));
	let temp_133_1 = (add_((mul_(b, (mul_(d, d)))), (mul_(a, (mul_(d, d))))));
	assert(eq_(temp_133_0, temp_133_1)) by {
		lemma_mul_dist(b, a, mul_(d, d));
	}
	let temp_134_0 = (mul_(b, (mul_(d, b))));
	let temp_134_1 = (mul_((mul_(b, d)), b));
	assert(eq_(temp_134_0, temp_134_1)) by {
		lemma_mul_assoc(b, d, b);
	}
	let temp_135_0 = (sub_((mul_(a, b)), (mul_(d, (mod_(c, m))))));
	let temp_135_1 = (sub_((mul_(a, b)), (mul_(d, (mod_((add_((mul_((mul_((add_(c, c)), (mul_((mod_(a, m)), b)))), m)), c)), m))))));
	assert(eq_(temp_135_0, temp_135_1)) by {
		lemma_mod_mul_vanish(c, mul_(add_(c, c), mul_(mod_(a, m), b)), m);
		cong_sub_(mul_(a, b), mul_(d, mod_(c, m)), mul_(a, b), mul_(d, mod_(add_(mul_(mul_(add_(c, c), mul_(mod_(a, m), b)), m), c), m)));
		lemma_eq_ref(d);
		lemma_eq_ref(mul_(a, b));
		cong_mul_(d, mod_(c, m), d, mod_(add_(mul_(mul_(add_(c, c), mul_(mod_(a, m), b)), m), c), m));
	}
	let temp_136_0 = (mul_((mod_(c, m)), (mul_(b, d))));
	let temp_136_1 = (mul_((mul_((mod_(c, m)), b)), d));
	assert(eq_(temp_136_0, temp_136_1)) by {
		lemma_mul_assoc(mod_(c, m), b, d);
	}
	let temp_137_0 = (mul_((mod_((mul_((mod_(a, m)), b)), m)), (mod_((add_(c, d)), m))));
	let temp_137_1 = (mul_((mod_((mul_(b, (mod_(a, m)))), m)), (mod_((add_(c, d)), m))));
	assert(eq_(temp_137_0, temp_137_1)) by {
		cong_mod_(mul_(mod_(a, m), b), m, mul_(b, mod_(a, m)), m);
		lemma_eq_ref(mod_(add_(c, d), m));
		lemma_mul_comm(mod_(a, m), b);
		cong_mul_(mod_(mul_(mod_(a, m), b), m), mod_(add_(c, d), m), mod_(mul_(b, mod_(a, m)), m), mod_(add_(c, d), m));
		lemma_eq_ref(m);
	}
	let temp_138_0 = (mul_((mul_(c, (mod_(b, m)))), (mul_(d, b))));
	let temp_138_1 = (mul_((mul_(c, (mod_((add_((mul_((mul_((mul_(a, b)), (mul_(b, (mod_(b, m)))))), m)), b)), m)))), (mul_(d, b))));
	assert(eq_(temp_138_0, temp_138_1)) by {
		lemma_mod_mul_vanish(b, mul_(mul_(a, b), mul_(b, mod_(b, m))), m);
		cong_mul_(mul_(c, mod_(b, m)), mul_(d, b), mul_(c, mod_(add_(mul_(mul_(mul_(a, b), mul_(b, mod_(b, m))), m), b), m)), mul_(d, b));
		lemma_eq_ref(c);
		cong_mul_(c, mod_(b, m), c, mod_(add_(mul_(mul_(mul_(a, b), mul_(b, mod_(b, m))), m), b), m));
		lemma_eq_ref(mul_(d, b));
	}
	let temp_139_0 = (mod_((sub_((mul_(a, (mod_(a, m)))), (add_(c, b)))), m));
	let temp_139_1 = (mod_((sub_((mod_((mul_(a, (mod_(a, m)))), m)), (mod_((add_(c, b)), m)))), m));
	assert(eq_(temp_139_0, temp_139_1)) by {
		lemma_mod_sub_noop(mul_(a, mod_(a, m)), add_(c, b), m);
	}
	let temp_140_0 = (mul_((mul_(b, b)), (mul_(a, a))));
	let temp_140_1 = (mul_((mul_(a, a)), (mul_(b, b))));
	assert(eq_(temp_140_0, temp_140_1)) by {
		lemma_mul_comm(mul_(b, b), mul_(a, a));
	}
	let temp_141_0 = (mul_((mul_(d, b)), (mul_(d, b))));
	let temp_141_1 = (mul_((mul_(d, b)), (mul_(d, b))));
	assert(eq_(temp_141_0, temp_141_1)) by {
		lemma_eq_ref(temp_141_0);
	}
	let temp_142_0 = (mul_((mod_((mul_(d, as_elem(15))), m)), c));
	let temp_142_1 = (mul_((mod_((sub_((mul_(d, as_elem(15))), (mul_((mul_((mul_(b, c)), (sub_(d, d)))), m)))), m)), c));
	assert(eq_(temp_142_0, temp_142_1)) by {
		lemma_mod_mul_vanish(mul_(d, as_elem(15)), mul_(mul_(b, c), sub_(d, d)), m);
		cong_mul_(mod_(mul_(d, as_elem(15)), m), c, mod_(sub_(mul_(d, as_elem(15)), mul_(mul_(mul_(b, c), sub_(d, d)), m)), m), c);
		lemma_eq_ref(c);
	}
	let temp_143_0 = (mul_((mul_(c, c)), (mul_(b, d))));
	let temp_143_1 = (mul_((mul_(b, d)), (mul_(c, c))));
	assert(eq_(temp_143_0, temp_143_1)) by {
		lemma_mul_comm(mul_(c, c), mul_(b, d));
	}
	let temp_144_0 = (mul_((mul_(b, a)), (mod_((sub_(d, d)), m))));
	let temp_144_1 = (mul_((mod_((sub_(d, d)), m)), (mul_(b, a))));
	assert(eq_(temp_144_0, temp_144_1)) by {
		lemma_mul_comm(mul_(b, a), mod_(sub_(d, d), m));
	}
	let temp_145_0 = (mod_((mul_((mul_((mod_(c, m)), b)), (mul_(b, b)))), m));
	let temp_145_1 = (mod_((mul_((mul_((mod_(c, m)), b)), (mul_(b, b)))), m));
	assert(eq_(temp_145_0, temp_145_1)) by {
		lemma_eq_ref(temp_145_0);
	}
	let temp_146_0 = (add_((mod_((mul_(a, b)), m)), (mul_(d, b))));
	let temp_146_1 = (add_((mod_((mul_(b, a)), m)), (mul_(d, b))));
	assert(eq_(temp_146_0, temp_146_1)) by {
		lemma_mul_comm(a, b);
		cong_add_(mod_(mul_(a, b), m), mul_(d, b), mod_(mul_(b, a), m), mul_(d, b));
		lemma_eq_ref(m);
		cong_mod_(mul_(a, b), m, mul_(b, a), m);
		lemma_eq_ref(mul_(d, b));
	}
	let temp_147_0 = (sub_((add_(c, b)), (mul_(d, b))));
	let temp_147_1 = (sub_((add_(b, c)), (mul_(d, b))));
	assert(eq_(temp_147_0, temp_147_1)) by {
		cong_sub_(add_(c, b), mul_(d, b), add_(b, c), mul_(d, b));
		lemma_add_comm(c, b);
		lemma_eq_ref(mul_(d, b));
	}
	let temp_148_0 = (mul_((mul_(d, d)), (mul_(a, (mod_(d, m))))));
	let temp_148_1 = (mul_((mul_(d, d)), (mul_(a, (mod_((sub_(d, (mul_((mul_((mul_(d, a)), (mul_(b, a)))), m)))), m))))));
	assert(eq_(temp_148_0, temp_148_1)) by {
		lemma_mul_comm(d, d);
		lemma_mod_mul_vanish(d, mul_(mul_(d, a), mul_(b, a)), m);
		cong_mul_(mul_(d, d), mul_(a, mod_(d, m)), mul_(d, d), mul_(a, mod_(sub_(d, mul_(mul_(mul_(d, a), mul_(b, a)), m)), m)));
		lemma_eq_ref(a);
		cong_mul_(a, mod_(d, m), a, mod_(sub_(d, mul_(mul_(mul_(d, a), mul_(b, a)), m)), m));
	}
	let temp_149_0 = (mul_((sub_(c, a)), (mul_(b, b))));
	let temp_149_1 = (mul_((mul_((sub_(c, a)), b)), b));
	assert(eq_(temp_149_0, temp_149_1)) by {
		lemma_mul_assoc(sub_(c, a), b, b);
	}

}

} // verus!