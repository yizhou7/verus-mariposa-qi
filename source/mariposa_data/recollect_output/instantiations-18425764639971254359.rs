use builtin_macros::*;
// use builtin::*;
mod nl_basics;
use crate::nl_basics::*;
verus! {

pub proof fn free_0(a: Elem, b: Elem, c: Elem, d: Elem, m: Elem)
{
	let temp_0_0 = (add_((sub_(a, d)), (sub_(a, d))));
	let temp_0_1 = (add_((sub_(a, d)), (sub_(a, d))));
	assert(eq_(temp_0_0, temp_0_1)) by {
		lemma_eq_ref(temp_0_0);
	}
	let temp_1_0 = (mul_((add_(a, c)), (mul_(d, d))));
	let temp_1_1 = (mul_((mul_(d, d)), (add_(a, c))));
	assert(eq_(temp_1_0, temp_1_1)) by {
		lemma_mul_comm(add_(a, c), mul_(d, d));
	}
	let temp_2_0 = (mul_((mul_(c, b)), (mul_(d, d))));
	let temp_2_1 = (mul_((mul_((mul_(c, b)), d)), d));
	assert(eq_(temp_2_0, temp_2_1)) by {
		lemma_mul_assoc(mul_(c, b), d, d);
	}
	let temp_3_0 = (mul_((mul_(d, a)), (sub_(as_elem(40), d))));
	let temp_3_1 = (mul_(d, (mul_(a, (sub_(as_elem(40), d))))));
	assert(eq_(temp_3_0, temp_3_1)) by {
		lemma_eq_sym(temp_3_1, temp_3_0);
		lemma_mul_assoc(d, a, sub_(as_elem(40), d));
	}
	let temp_4_0 = (mul_((mul_(d, (mod_(b, m)))), (mul_(c, as_elem(39)))));
	let temp_4_1 = (mul_((mul_((mul_(d, (mod_(b, m)))), c)), as_elem(39)));
	assert(eq_(temp_4_0, temp_4_1)) by {
		lemma_mul_assoc(mul_(d, mod_(b, m)), c, as_elem(39));
	}
	let temp_5_0 = (mul_((mul_(c, c)), (mul_(a, d))));
	let temp_5_1 = (mul_((mul_((mul_(c, c)), a)), d));
	assert(eq_(temp_5_0, temp_5_1)) by {
		lemma_mul_assoc(mul_(c, c), a, d);
	}
	let temp_6_0 = (mul_((mul_(a, d)), (mul_(c, d))));
	let temp_6_1 = (mul_((mul_(d, a)), (mul_(c, d))));
	assert(eq_(temp_6_0, temp_6_1)) by {
		cong_mul_(mul_(a, d), mul_(c, d), mul_(d, a), mul_(c, d));
		lemma_mul_comm(a, d);
		lemma_eq_ref(mul_(c, d));
	}
	let temp_7_0 = (add_((mul_(d, (mod_(b, m)))), (mul_(b, c))));
	let temp_7_1 = (add_((mul_((mod_(b, m)), d)), (mul_(b, c))));
	assert(eq_(temp_7_0, temp_7_1)) by {
		lemma_mul_comm(d, mod_(b, m));
		cong_add_(mul_(d, mod_(b, m)), mul_(b, c), mul_(mod_(b, m), d), mul_(b, c));
		lemma_eq_ref(mul_(b, c));
	}
	let temp_8_0 = (mul_((mul_(c, b)), (mul_(b, (mod_(d, m))))));
	let temp_8_1 = (mul_((mul_((mul_(c, b)), b)), (mod_(d, m))));
	assert(eq_(temp_8_0, temp_8_1)) by {
		lemma_mul_assoc(mul_(c, b), b, mod_(d, m));
	}
	let temp_9_0 = (mul_((add_(d, a)), (mul_(c, as_elem(81)))));
	let temp_9_1 = (mul_((add_(d, a)), (mul_(as_elem(81), c))));
	assert(eq_(temp_9_0, temp_9_1)) by {
		lemma_mul_comm(c, as_elem(81));
		cong_mul_(add_(d, a), mul_(c, as_elem(81)), add_(d, a), mul_(as_elem(81), c));
		lemma_eq_ref(add_(d, a));
	}
	let temp_10_0 = (mul_((mul_((mod_(a, m)), b)), (mul_(d, b))));
	let temp_10_1 = (mul_((mul_((mul_((mod_(a, m)), b)), d)), b));
	assert(eq_(temp_10_0, temp_10_1)) by {
		lemma_mul_assoc(mul_(mod_(a, m), b), d, b);
	}
	let temp_11_0 = (mod_((mul_((mul_(c, d)), (mul_(d, (mod_(d, m)))))), m));
	let temp_11_1 = (mod_((mul_((mul_(c, d)), (mul_((mod_(d, m)), d)))), m));
	assert(eq_(temp_11_0, temp_11_1)) by {
		lemma_mul_comm(d, mod_(d, m));
		cong_mod_(mul_(mul_(c, d), mul_(d, mod_(d, m))), m, mul_(mul_(c, d), mul_(mod_(d, m), d)), m);
		lemma_eq_ref(mul_(c, d));
		cong_mul_(mul_(c, d), mul_(d, mod_(d, m)), mul_(c, d), mul_(mod_(d, m), d));
		lemma_eq_ref(m);
	}
	let temp_12_0 = (mul_((sub_(a, b)), (sub_(a, a))));
	let temp_12_1 = (mul_((sub_(a, a)), (sub_(a, b))));
	assert(eq_(temp_12_0, temp_12_1)) by {
		lemma_mul_comm(sub_(a, b), sub_(a, a));
	}
	let temp_13_0 = (mul_((mul_(c, c)), (mul_(d, a))));
	let temp_13_1 = (mul_((mul_(d, a)), (mul_(c, c))));
	assert(eq_(temp_13_0, temp_13_1)) by {
		lemma_mul_comm(mul_(c, c), mul_(d, a));
	}
	let temp_14_0 = (mul_((mul_(c, a)), (mul_(d, b))));
	let temp_14_1 = (mul_(c, (mul_(a, (mul_(d, b))))));
	assert(eq_(temp_14_0, temp_14_1)) by {
		lemma_eq_sym(temp_14_1, temp_14_0);
		lemma_mul_assoc(c, a, mul_(d, b));
	}
	let temp_15_0 = (mul_((mul_((mod_(b, m)), d)), (mod_((mul_(d, (mod_(d, m)))), m))));
	let temp_15_1 = (mul_((mul_(d, (mod_(b, m)))), (mod_((mul_(d, (mod_(d, m)))), m))));
	assert(eq_(temp_15_0, temp_15_1)) by {
		lemma_mul_comm(mod_(b, m), d);
		cong_mul_(mul_(mod_(b, m), d), mod_(mul_(d, mod_(d, m)), m), mul_(d, mod_(b, m)), mod_(mul_(d, mod_(d, m)), m));
		lemma_eq_ref(mod_(mul_(d, mod_(d, m)), m));
	}
	let temp_16_0 = (mul_((mul_(a, b)), (add_(a, c))));
	let temp_16_1 = (mul_((mul_(a, b)), (add_(c, a))));
	assert(eq_(temp_16_0, temp_16_1)) by {
		cong_mul_(mul_(a, b), add_(a, c), mul_(a, b), add_(c, a));
		lemma_add_comm(a, c);
		lemma_eq_ref(mul_(a, b));
	}
	let temp_17_0 = (mul_((mod_((add_(b, (mod_(b, m)))), m)), (mul_(a, c))));
	let temp_17_1 = (mul_((mod_((add_((mod_(b, m)), (mod_((mod_(b, m)), m)))), m)), (mul_(a, c))));
	assert(eq_(temp_17_0, temp_17_1)) by {
		lemma_mod_add_noop(b, mod_(b, m), m);
		cong_mul_(mod_(add_(b, mod_(b, m)), m), mul_(a, c), mod_(add_(mod_(b, m), mod_(mod_(b, m), m)), m), mul_(a, c));
		lemma_eq_ref(mul_(a, c));
	}
	let temp_18_0 = (mul_((mul_(b, a)), (add_(a, c))));
	let temp_18_1 = (mul_(b, (mul_(a, (add_(a, c))))));
	assert(eq_(temp_18_0, temp_18_1)) by {
		lemma_eq_sym(temp_18_1, temp_18_0);
		lemma_mul_assoc(b, a, add_(a, c));
	}
	let temp_19_0 = (add_((mul_(c, c)), (mul_(c, (mod_(d, m))))));
	let temp_19_1 = (add_((mul_(c, (mod_(d, m)))), (mul_(c, c))));
	assert(eq_(temp_19_0, temp_19_1)) by {
		lemma_add_comm(mul_(c, c), mul_(c, mod_(d, m)));
	}
	let temp_20_0 = (mul_((mul_(b, c)), (mod_((mul_(b, d)), m))));
	let temp_20_1 = (mul_(b, (mul_(c, (mod_((mul_(b, d)), m))))));
	assert(eq_(temp_20_0, temp_20_1)) by {
		lemma_mul_assoc(b, c, mod_(mul_(b, d), m));
		lemma_eq_sym(temp_20_1, temp_20_0);
	}
	let temp_21_0 = (mod_((mul_((mul_(d, (mod_(a, m)))), (mul_((mod_(b, m)), a)))), m));
	let temp_21_1 = (mod_((mul_((mul_(d, (mod_(a, m)))), (mul_((mod_((sub_(b, (mul_((sub_((mul_(b, a)), (mod_((mul_(c, b)), m)))), m)))), m)), a)))), m));
	assert(eq_(temp_21_0, temp_21_1)) by {
		cong_mul_(mod_(b, m), a, mod_(sub_(b, mul_(sub_(mul_(b, a), mod_(mul_(c, b), m)), m)), m), a);
		cong_mul_(mul_(d, mod_(a, m)), mul_(mod_(b, m), a), mul_(d, mod_(a, m)), mul_(mod_(sub_(b, mul_(sub_(mul_(b, a), mod_(mul_(c, b), m)), m)), m), a));
		lemma_eq_ref(mul_(d, mod_(a, m)));
		lemma_eq_ref(a);
		lemma_eq_ref(m);
		lemma_mod_mul_vanish(b, sub_(mul_(b, a), mod_(mul_(c, b), m)), m);
		cong_mod_(mul_(mul_(d, mod_(a, m)), mul_(mod_(b, m), a)), m, mul_(mul_(d, mod_(a, m)), mul_(mod_(sub_(b, mul_(sub_(mul_(b, a), mod_(mul_(c, b), m)), m)), m), a)), m);
	}
	let temp_22_0 = (mul_((mul_(a, b)), (mul_(d, (mod_(c, m))))));
	let temp_22_1 = (mul_((mul_(d, (mod_(c, m)))), (mul_(a, b))));
	assert(eq_(temp_22_0, temp_22_1)) by {
		lemma_mul_comm(mul_(a, b), mul_(d, mod_(c, m)));
	}
	let temp_23_0 = (sub_((mul_(a, d)), (mul_(a, c))));
	let temp_23_1 = (sub_((mul_(a, d)), (mul_(c, a))));
	assert(eq_(temp_23_0, temp_23_1)) by {
		cong_sub_(mul_(a, d), mul_(a, c), mul_(a, d), mul_(c, a));
		lemma_mul_comm(a, c);
		lemma_eq_ref(mul_(a, d));
	}
	let temp_24_0 = (add_((mod_((mul_(a, d)), m)), (mul_(as_elem(87), d))));
	let temp_24_1 = (add_((mod_((mul_(a, d)), m)), (mul_(d, as_elem(87)))));
	assert(eq_(temp_24_0, temp_24_1)) by {
		lemma_mul_comm(as_elem(87), d);
		cong_add_(mod_(mul_(a, d), m), mul_(as_elem(87), d), mod_(mul_(a, d), m), mul_(d, as_elem(87)));
		lemma_eq_ref(mod_(mul_(a, d), m));
	}
	let temp_25_0 = (mul_((add_((mod_(a, m)), b)), (mul_(a, d))));
	let temp_25_1 = (mul_((mul_((add_((mod_(a, m)), b)), a)), d));
	assert(eq_(temp_25_0, temp_25_1)) by {
		lemma_mul_assoc(add_(mod_(a, m), b), a, d);
	}
	let temp_26_0 = (mul_((mul_(d, b)), (mod_((mul_(b, c)), m))));
	let temp_26_1 = (mul_((mul_(d, b)), (mod_((add_((mul_((mul_((sub_((mod_(d, m)), c)), (mul_(c, b)))), m)), (mul_(b, c)))), m))));
	assert(eq_(temp_26_0, temp_26_1)) by {
		lemma_mod_mul_vanish(mul_(b, c), mul_(sub_(mod_(d, m), c), mul_(c, b)), m);
		cong_mul_(mul_(d, b), mod_(mul_(b, c), m), mul_(d, b), mod_(add_(mul_(mul_(sub_(mod_(d, m), c), mul_(c, b)), m), mul_(b, c)), m));
		lemma_eq_ref(mul_(d, b));
	}
	let temp_27_0 = (mul_((sub_(c, b)), (mul_(d, b))));
	let temp_27_1 = (mul_((mul_(d, b)), (sub_(c, b))));
	assert(eq_(temp_27_0, temp_27_1)) by {
		lemma_mul_comm(sub_(c, b), mul_(d, b));
	}
	let temp_28_0 = (mul_(as_elem(7), (mod_((add_(a, d)), m))));
	let temp_28_1 = (mul_(as_elem(7), (mod_((add_((mod_(a, m)), (mod_(d, m)))), m))));
	assert(eq_(temp_28_0, temp_28_1)) by {
		lemma_mod_add_noop(a, d, m);
		cong_mul_(as_elem(7), mod_(add_(a, d), m), as_elem(7), mod_(add_(mod_(a, m), mod_(d, m)), m));
		lemma_eq_ref(as_elem(7));
	}
	let temp_29_0 = (mul_((mod_((mul_((mod_(a, m)), d)), m)), (mul_(as_elem(52), c))));
	let temp_29_1 = (mul_((mod_((mul_((mod_(a, m)), d)), m)), (mul_(c, as_elem(52)))));
	assert(eq_(temp_29_0, temp_29_1)) by {
		lemma_mul_comm(as_elem(52), c);
		cong_mul_(mod_(mul_(mod_(a, m), d), m), mul_(as_elem(52), c), mod_(mul_(mod_(a, m), d), m), mul_(c, as_elem(52)));
		lemma_eq_ref(mod_(mul_(mod_(a, m), d), m));
	}
	let temp_30_0 = (mul_((mul_(a, a)), (mul_(as_elem(54), b))));
	let temp_30_1 = (mul_(a, (mul_(a, (mul_(as_elem(54), b))))));
	assert(eq_(temp_30_0, temp_30_1)) by {
		lemma_eq_sym(temp_30_1, temp_30_0);
		lemma_mul_assoc(a, a, mul_(as_elem(54), b));
	}
	let temp_31_0 = (mul_((mul_(c, b)), (mul_(a, a))));
	let temp_31_1 = (mul_((mul_((mul_(c, b)), a)), a));
	assert(eq_(temp_31_0, temp_31_1)) by {
		lemma_mul_assoc(mul_(c, b), a, a);
	}
	let temp_32_0 = (add_((sub_(c, (mod_(a, m)))), (mul_(c, (mod_(d, m))))));
	let temp_32_1 = (add_((sub_(c, (mod_(a, m)))), (mul_((mod_(d, m)), c))));
	assert(eq_(temp_32_0, temp_32_1)) by {
		lemma_mul_comm(c, mod_(d, m));
		cong_add_(sub_(c, mod_(a, m)), mul_(c, mod_(d, m)), sub_(c, mod_(a, m)), mul_(mod_(d, m), c));
		lemma_eq_ref(sub_(c, mod_(a, m)));
	}
	let temp_33_0 = (sub_((mod_((mul_(c, d)), m)), (sub_(d, d))));
	let temp_33_1 = (sub_((mod_((add_((mul_(c, d)), (mul_((add_((mul_(d, b)), (sub_(a, c)))), m)))), m)), (sub_(d, d))));
	assert(eq_(temp_33_0, temp_33_1)) by {
		lemma_mod_mul_vanish(mul_(c, d), add_(mul_(d, b), sub_(a, c)), m);
		cong_sub_(mod_(mul_(c, d), m), sub_(d, d), mod_(add_(mul_(c, d), mul_(add_(mul_(d, b), sub_(a, c)), m)), m), sub_(d, d));
		lemma_eq_ref(sub_(d, d));
	}
	let temp_34_0 = (mul_((mul_((mod_(d, m)), d)), (mul_(b, c))));
	let temp_34_1 = (mul_((mul_((mod_(d, m)), d)), (mul_(c, b))));
	assert(eq_(temp_34_0, temp_34_1)) by {
		lemma_mul_comm(b, c);
		cong_mul_(mul_(mod_(d, m), d), mul_(b, c), mul_(mod_(d, m), d), mul_(c, b));
		lemma_eq_ref(mul_(mod_(d, m), d));
	}
	let temp_35_0 = (mul_((mod_((sub_(d, c)), m)), (mul_((mod_(a, m)), d))));
	let temp_35_1 = (mul_((mod_((sub_((mod_(d, m)), c)), m)), (mul_((mod_(a, m)), d))));
	assert(eq_(temp_35_0, temp_35_1)) by {
		cong_mul_(mod_(sub_(d, c), m), mul_(mod_(a, m), d), mod_(sub_(mod_(d, m), c), m), mul_(mod_(a, m), d));
		lemma_mod_sub_noop(d, c, m);
		lemma_eq_ref(mul_(mod_(a, m), d));
	}
	let temp_36_0 = (mul_((add_(a, a)), (mul_((mod_(a, m)), c))));
	let temp_36_1 = (mul_((add_(a, a)), (mul_((mod_(a, m)), c))));
	assert(eq_(temp_36_0, temp_36_1)) by {
		lemma_eq_ref(temp_36_0);
	}
	let temp_37_0 = (mul_((add_(b, a)), (mul_((mod_(c, m)), c))));
	let temp_37_1 = (mul_((mul_((mod_(c, m)), c)), (add_(b, a))));
	assert(eq_(temp_37_0, temp_37_1)) by {
		lemma_mul_comm(add_(b, a), mul_(mod_(c, m), c));
	}
	let temp_38_0 = (mul_((mul_(c, a)), (mul_(b, d))));
	let temp_38_1 = (mul_((mul_(c, a)), (mul_(d, b))));
	assert(eq_(temp_38_0, temp_38_1)) by {
		cong_mul_(mul_(c, a), mul_(b, d), mul_(c, a), mul_(d, b));
		lemma_mul_comm(b, d);
		lemma_eq_ref(mul_(c, a));
	}
	let temp_39_0 = (sub_((add_(c, a)), (mul_(c, d))));
	let temp_39_1 = (sub_((add_(c, a)), (mul_(d, c))));
	assert(eq_(temp_39_0, temp_39_1)) by {
		cong_sub_(add_(c, a), mul_(c, d), add_(c, a), mul_(d, c));
		lemma_mul_comm(c, d);
		lemma_eq_ref(add_(c, a));
	}
	let temp_40_0 = (mul_((mod_((mul_(a, b)), m)), (mul_(b, b))));
	let temp_40_1 = (mul_((mul_((mod_((mul_(a, b)), m)), b)), b));
	assert(eq_(temp_40_0, temp_40_1)) by {
		lemma_mul_assoc(mod_(mul_(a, b), m), b, b);
	}
	let temp_41_0 = (add_((mul_(a, c)), (mul_(c, a))));
	let temp_41_1 = (add_((mul_(c, a)), (mul_(a, c))));
	assert(eq_(temp_41_0, temp_41_1)) by {
		lemma_add_comm(mul_(a, c), mul_(c, a));
	}
	let temp_42_0 = (mul_((sub_(c, a)), (add_((mod_(c, m)), b))));
	let temp_42_1 = (mul_((add_((mod_(c, m)), b)), (sub_(c, a))));
	assert(eq_(temp_42_0, temp_42_1)) by {
		lemma_mul_comm(sub_(c, a), add_(mod_(c, m), b));
	}
	let temp_43_0 = (mul_((mod_((mul_(b, d)), m)), (mul_(b, (mod_(d, m))))));
	let temp_43_1 = (mul_((mul_((mod_((mul_(b, d)), m)), b)), (mod_(d, m))));
	assert(eq_(temp_43_0, temp_43_1)) by {
		lemma_mul_assoc(mod_(mul_(b, d), m), b, mod_(d, m));
	}
	let temp_44_0 = (add_((mul_(d, a)), (mul_(d, b))));
	let temp_44_1 = (add_((mul_(d, b)), (mul_(d, a))));
	assert(eq_(temp_44_0, temp_44_1)) by {
		lemma_add_comm(mul_(d, a), mul_(d, b));
	}
	let temp_45_0 = (add_((mul_((mod_(b, m)), a)), (mul_(a, a))));
	let temp_45_1 = (mul_((add_((mod_(b, m)), a)), a));
	assert(eq_(temp_45_0, temp_45_1)) by {
		lemma_eq_sym(temp_45_1, temp_45_0);
		lemma_mul_dist(mod_(b, m), a, a);
	}
	let temp_46_0 = (mul_((add_(b, c)), (mul_(d, c))));
	let temp_46_1 = (mul_((add_(c, b)), (mul_(d, c))));
	assert(eq_(temp_46_0, temp_46_1)) by {
		cong_mul_(add_(b, c), mul_(d, c), add_(c, b), mul_(d, c));
		lemma_add_comm(b, c);
		lemma_eq_ref(mul_(d, c));
	}
	let temp_47_0 = (mul_((mul_(d, d)), (mul_(b, a))));
	let temp_47_1 = (mul_((mul_(d, d)), (mul_(b, a))));
	assert(eq_(temp_47_0, temp_47_1)) by {
		lemma_eq_ref(temp_47_0);
	}
	let temp_48_0 = (mul_((add_(b, b)), (mul_(b, a))));
	let temp_48_1 = (mul_((add_(b, b)), (mul_(b, a))));
	assert(eq_(temp_48_0, temp_48_1)) by {
		lemma_eq_ref(temp_48_0);
	}
	let temp_49_0 = (mul_((mul_(d, b)), (add_(b, d))));
	let temp_49_1 = (add_((mul_((mul_(d, b)), b)), (mul_((mul_(d, b)), d))));
	assert(eq_(temp_49_0, temp_49_1)) by {
		lemma_mul_dist(mul_(d, b), b, d);
	}
	let temp_50_0 = (mul_((mul_(c, c)), (mul_(d, a))));
	let temp_50_1 = (mul_((mul_(c, c)), (mul_(a, d))));
	assert(eq_(temp_50_0, temp_50_1)) by {
		cong_mul_(mul_(c, c), mul_(d, a), mul_(c, c), mul_(a, d));
		lemma_mul_comm(c, c);
		lemma_mul_comm(d, a);
	}
	let temp_51_0 = (mul_((mul_(d, b)), (mul_(c, (mod_(b, m))))));
	let temp_51_1 = (mul_((mul_(c, (mod_(b, m)))), (mul_(d, b))));
	assert(eq_(temp_51_0, temp_51_1)) by {
		lemma_mul_comm(mul_(d, b), mul_(c, mod_(b, m)));
	}
	let temp_52_0 = (mul_((add_(b, d)), (mod_((mul_(a, c)), m))));
	let temp_52_1 = (mul_((add_(b, d)), (mod_((sub_((mul_(a, c)), (mul_((mul_((mul_(c, d)), (mul_(c, d)))), m)))), m))));
	assert(eq_(temp_52_0, temp_52_1)) by {
		lemma_mod_mul_vanish(mul_(a, c), mul_(mul_(c, d), mul_(c, d)), m);
		cong_mul_(add_(b, d), mod_(mul_(a, c), m), add_(b, d), mod_(sub_(mul_(a, c), mul_(mul_(mul_(c, d), mul_(c, d)), m)), m));
		lemma_eq_ref(add_(b, d));
	}
	let temp_53_0 = (mul_((mul_(d, a)), (mul_(a, c))));
	let temp_53_1 = (mul_((mul_(a, d)), (mul_(a, c))));
	assert(eq_(temp_53_0, temp_53_1)) by {
		cong_mul_(mul_(d, a), mul_(a, c), mul_(a, d), mul_(a, c));
		lemma_mul_comm(d, a);
		lemma_eq_ref(mul_(a, c));
	}
	let temp_54_0 = (mul_((add_(c, c)), (mul_((mod_(c, m)), d))));
	let temp_54_1 = (mul_((add_(c, c)), (mul_((mod_((add_((mul_((mul_((mul_(b, b)), (mul_(d, c)))), m)), c)), m)), d))));
	assert(eq_(temp_54_0, temp_54_1)) by {
		lemma_add_comm(c, c);
		lemma_mod_mul_vanish(c, mul_(mul_(b, b), mul_(d, c)), m);
		cong_mul_(add_(c, c), mul_(mod_(c, m), d), add_(c, c), mul_(mod_(add_(mul_(mul_(mul_(b, b), mul_(d, c)), m), c), m), d));
		lemma_eq_ref(d);
		cong_mul_(mod_(c, m), d, mod_(add_(mul_(mul_(mul_(b, b), mul_(d, c)), m), c), m), d);
	}
	let temp_55_0 = (add_((mul_(c, b)), (mod_((mul_(b, a)), m))));
	let temp_55_1 = (add_((mul_(c, b)), (mod_((add_((mul_(b, a)), (mul_((mul_((mul_(b, b)), (mul_(d, d)))), m)))), m))));
	assert(eq_(temp_55_0, temp_55_1)) by {
		lemma_mod_mul_vanish(mul_(b, a), mul_(mul_(b, b), mul_(d, d)), m);
		cong_add_(mul_(c, b), mod_(mul_(b, a), m), mul_(c, b), mod_(add_(mul_(b, a), mul_(mul_(mul_(b, b), mul_(d, d)), m)), m));
		lemma_eq_ref(mul_(c, b));
	}
	let temp_56_0 = (mul_((mul_(c, a)), (sub_(b, (mod_(c, m))))));
	let temp_56_1 = (mul_(c, (mul_(a, (sub_(b, (mod_(c, m))))))));
	assert(eq_(temp_56_0, temp_56_1)) by {
		lemma_mul_assoc(c, a, sub_(b, mod_(c, m)));
		lemma_eq_sym(temp_56_1, temp_56_0);
	}
	let temp_57_0 = (mul_((mul_(a, (mod_(c, m)))), (mul_(c, a))));
	let temp_57_1 = (mul_((mul_(a, (mod_((add_(c, (mul_((mul_((mul_(a, c)), (mul_(a, b)))), m)))), m)))), (mul_(c, a))));
	assert(eq_(temp_57_0, temp_57_1)) by {
		lemma_mod_mul_vanish(c, mul_(mul_(a, c), mul_(a, b)), m);
		cong_mul_(mul_(a, mod_(c, m)), mul_(c, a), mul_(a, mod_(add_(c, mul_(mul_(mul_(a, c), mul_(a, b)), m)), m)), mul_(c, a));
		lemma_eq_ref(mul_(c, a));
		lemma_eq_ref(a);
		cong_mul_(a, mod_(c, m), a, mod_(add_(c, mul_(mul_(mul_(a, c), mul_(a, b)), m)), m));
	}
	let temp_58_0 = (mod_((mul_((mul_(d, a)), (mul_(b, (mod_(c, m)))))), m));
	let temp_58_1 = (mod_((mul_((mul_(b, (mod_(c, m)))), (mul_(d, a)))), m));
	assert(eq_(temp_58_0, temp_58_1)) by {
		lemma_mul_comm(mul_(d, a), mul_(b, mod_(c, m)));
		cong_mod_(mul_(mul_(d, a), mul_(b, mod_(c, m))), m, mul_(mul_(b, mod_(c, m)), mul_(d, a)), m);
		lemma_eq_ref(m);
	}
	let temp_59_0 = (mul_((mul_(a, d)), (mod_((mul_(b, d)), m))));
	let temp_59_1 = (mul_((mul_(a, d)), (mod_((mul_(d, b)), m))));
	assert(eq_(temp_59_0, temp_59_1)) by {
		lemma_mul_comm(b, d);
		cong_mul_(mul_(a, d), mod_(mul_(b, d), m), mul_(a, d), mod_(mul_(d, b), m));
		lemma_eq_ref(mul_(a, d));
		cong_mod_(mul_(b, d), m, mul_(d, b), m);
		lemma_eq_ref(m);
	}
	let temp_60_0 = (add_((sub_(a, a)), (mul_(d, c))));
	let temp_60_1 = (add_((sub_(a, a)), (mul_(c, d))));
	assert(eq_(temp_60_0, temp_60_1)) by {
		cong_add_(sub_(a, a), mul_(d, c), sub_(a, a), mul_(c, d));
		lemma_mul_comm(d, c);
		lemma_eq_ref(sub_(a, a));
	}
	let temp_61_0 = (mul_((mul_((mod_(d, m)), c)), (mul_(as_elem(16), d))));
	let temp_61_1 = (mul_((mod_(d, m)), (mul_(c, (mul_(as_elem(16), d))))));
	assert(eq_(temp_61_0, temp_61_1)) by {
		lemma_mul_assoc(mod_(d, m), c, mul_(as_elem(16), d));
		lemma_eq_sym(temp_61_1, temp_61_0);
	}
	let temp_62_0 = (mul_((mul_((mod_(d, m)), a)), (mul_(c, b))));
	let temp_62_1 = (mul_((mul_((mul_((mod_(d, m)), a)), c)), b));
	assert(eq_(temp_62_0, temp_62_1)) by {
		lemma_mul_assoc(mul_(mod_(d, m), a), c, b);
	}
	let temp_63_0 = (mul_((sub_(b, c)), (mul_((mod_(b, m)), b))));
	let temp_63_1 = (sub_((mul_(b, (mul_((mod_(b, m)), b)))), (mul_(c, (mul_((mod_(b, m)), b))))));
	assert(eq_(temp_63_0, temp_63_1)) by {
		lemma_mul_dist(mul_(mod_(b, m), b), b, c);
	}
	let temp_64_0 = (mul_((mul_(c, a)), (add_(b, c))));
	let temp_64_1 = (mul_((mul_(c, a)), (add_(c, b))));
	assert(eq_(temp_64_0, temp_64_1)) by {
		cong_mul_(mul_(c, a), add_(b, c), mul_(c, a), add_(c, b));
		lemma_add_comm(b, c);
		lemma_eq_ref(mul_(c, a));
	}
	let temp_65_0 = (mul_((mul_(b, c)), (mul_(d, (mod_(b, m))))));
	let temp_65_1 = (mul_((mul_(b, c)), (mul_(d, (mod_((sub_(b, (mul_((mul_((mul_(b, a)), (mul_((mod_(d, m)), a)))), m)))), m))))));
	assert(eq_(temp_65_0, temp_65_1)) by {
		lemma_mod_mul_vanish(b, mul_(mul_(b, a), mul_(mod_(d, m), a)), m);
		cong_mul_(mul_(b, c), mul_(d, mod_(b, m)), mul_(b, c), mul_(d, mod_(sub_(b, mul_(mul_(mul_(b, a), mul_(mod_(d, m), a)), m)), m)));
		lemma_eq_ref(d);
		lemma_eq_ref(mul_(b, c));
		cong_mul_(d, mod_(b, m), d, mod_(sub_(b, mul_(mul_(mul_(b, a), mul_(mod_(d, m), a)), m)), m));
	}
	let temp_66_0 = (mul_((mod_((mul_(b, c)), m)), (mul_(b, c))));
	let temp_66_1 = (mul_((mod_((add_((mul_(b, c)), (mul_((mod_((mul_((mul_(c, a)), (mul_(a, c)))), m)), m)))), m)), (mul_(b, c))));
	assert(eq_(temp_66_0, temp_66_1)) by {
		lemma_mod_mul_vanish(mul_(b, c), mod_(mul_(mul_(c, a), mul_(a, c)), m), m);
		cong_mul_(mod_(mul_(b, c), m), mul_(b, c), mod_(add_(mul_(b, c), mul_(mod_(mul_(mul_(c, a), mul_(a, c)), m), m)), m), mul_(b, c));
		lemma_eq_ref(mul_(b, c));
	}
	let temp_67_0 = (mod_((mul_((mod_((add_(c, c)), m)), (mul_(a, c)))), m));
	let temp_67_1 = (mod_((mul_((mod_((add_(c, (mod_(c, m)))), m)), (mul_(a, c)))), m));
	assert(eq_(temp_67_0, temp_67_1)) by {
		lemma_mod_add_noop(c, c, m);
		cong_mod_(mul_(mod_(add_(c, c), m), mul_(a, c)), m, mul_(mod_(add_(c, mod_(c, m)), m), mul_(a, c)), m);
		lemma_eq_ref(mul_(a, c));
		cong_mul_(mod_(add_(c, c), m), mul_(a, c), mod_(add_(c, mod_(c, m)), m), mul_(a, c));
		lemma_eq_ref(m);
	}
	let temp_68_0 = (sub_((mul_(a, c)), (sub_((mod_(b, m)), c))));
	let temp_68_1 = (sub_((mul_(c, a)), (sub_((mod_(b, m)), c))));
	assert(eq_(temp_68_0, temp_68_1)) by {
		lemma_mul_comm(a, c);
		cong_sub_(mul_(a, c), sub_(mod_(b, m), c), mul_(c, a), sub_(mod_(b, m), c));
		lemma_eq_ref(sub_(mod_(b, m), c));
	}
	let temp_69_0 = (mul_((mul_(b, b)), (mul_(d, (mod_(c, m))))));
	let temp_69_1 = (mul_(b, (mul_(b, (mul_(d, (mod_(c, m))))))));
	assert(eq_(temp_69_0, temp_69_1)) by {
		lemma_mul_assoc(b, b, mul_(d, mod_(c, m)));
		lemma_eq_sym(temp_69_1, temp_69_0);
	}
	let temp_70_0 = (mul_((mul_(c, b)), (mod_((sub_(d, c)), m))));
	let temp_70_1 = (mul_((mul_(b, c)), (mod_((sub_(d, c)), m))));
	assert(eq_(temp_70_0, temp_70_1)) by {
		lemma_mul_comm(c, b);
		cong_mul_(mul_(c, b), mod_(sub_(d, c), m), mul_(b, c), mod_(sub_(d, c), m));
		lemma_eq_ref(mod_(sub_(d, c), m));
	}
	let temp_71_0 = (add_((add_(d, a)), (mul_(d, b))));
	let temp_71_1 = (add_((mul_(d, b)), (add_(d, a))));
	assert(eq_(temp_71_0, temp_71_1)) by {
		lemma_add_comm(add_(d, a), mul_(d, b));
	}
	let temp_72_0 = (mul_((mul_(b, a)), (mul_(c, (mod_(b, m))))));
	let temp_72_1 = (mul_((mul_(b, a)), (mul_(c, (mod_((add_(b, (mul_((mul_((mul_(b, d)), (mul_(d, b)))), m)))), m))))));
	assert(eq_(temp_72_0, temp_72_1)) by {
		lemma_mod_mul_vanish(b, mul_(mul_(b, d), mul_(d, b)), m);
		cong_mul_(mul_(b, a), mul_(c, mod_(b, m)), mul_(b, a), mul_(c, mod_(add_(b, mul_(mul_(mul_(b, d), mul_(d, b)), m)), m)));
		lemma_eq_ref(c);
		lemma_eq_ref(mul_(b, a));
		cong_mul_(c, mod_(b, m), c, mod_(add_(b, mul_(mul_(mul_(b, d), mul_(d, b)), m)), m));
	}
	let temp_73_0 = (mul_((add_(a, (mod_(d, m)))), (mul_(b, b))));
	let temp_73_1 = (mul_((mul_((add_(a, (mod_(d, m)))), b)), b));
	assert(eq_(temp_73_0, temp_73_1)) by {
		lemma_mul_assoc(add_(a, mod_(d, m)), b, b);
	}
	let temp_74_0 = (mul_((mul_(c, d)), (add_((mod_(a, m)), b))));
	let temp_74_1 = (mul_((mul_(c, d)), (add_(b, (mod_(a, m))))));
	assert(eq_(temp_74_0, temp_74_1)) by {
		lemma_add_comm(mod_(a, m), b);
		cong_mul_(mul_(c, d), add_(mod_(a, m), b), mul_(c, d), add_(b, mod_(a, m)));
		lemma_eq_ref(mul_(c, d));
	}
	let temp_75_0 = (mod_((mul_((mul_(a, b)), (mul_(c, (mod_(d, m)))))), m));
	let temp_75_1 = (mod_((mul_((mul_(a, b)), (mul_((mod_(d, m)), c)))), m));
	assert(eq_(temp_75_0, temp_75_1)) by {
		lemma_mul_comm(c, mod_(d, m));
		cong_mod_(mul_(mul_(a, b), mul_(c, mod_(d, m))), m, mul_(mul_(a, b), mul_(mod_(d, m), c)), m);
		lemma_eq_ref(mul_(a, b));
		lemma_eq_ref(m);
		cong_mul_(mul_(a, b), mul_(c, mod_(d, m)), mul_(a, b), mul_(mod_(d, m), c));
	}
	let temp_76_0 = (sub_((mul_(b, d)), (mul_(d, b))));
	let temp_76_1 = (sub_((mul_(b, d)), (mul_(b, d))));
	assert(eq_(temp_76_0, temp_76_1)) by {
		cong_sub_(mul_(b, d), mul_(d, b), mul_(b, d), mul_(b, d));
		lemma_mul_comm(d, b);
		lemma_eq_ref(mul_(b, d));
	}
	let temp_77_0 = (mod_((mul_((mod_((mul_(c, d)), m)), (add_((mod_(b, m)), d)))), m));
	let temp_77_1 = (mod_((mul_((mod_((mul_(c, d)), m)), (add_(d, (mod_(b, m)))))), m));
	assert(eq_(temp_77_0, temp_77_1)) by {
		lemma_add_comm(mod_(b, m), d);
		cong_mod_(mul_(mod_(mul_(c, d), m), add_(mod_(b, m), d)), m, mul_(mod_(mul_(c, d), m), add_(d, mod_(b, m))), m);
		lemma_eq_ref(mod_(mul_(c, d), m));
		cong_mul_(mod_(mul_(c, d), m), add_(mod_(b, m), d), mod_(mul_(c, d), m), add_(d, mod_(b, m)));
		lemma_eq_ref(m);
	}
	let temp_78_0 = (mul_((mul_(b, (mod_(b, m)))), (mod_((mul_(c, a)), m))));
	let temp_78_1 = (mul_((mul_(b, (mod_((add_(b, (mul_((mul_((sub_(a, d)), (mul_((mod_(a, m)), c)))), m)))), m)))), (mod_((mul_(c, a)), m))));
	assert(eq_(temp_78_0, temp_78_1)) by {
		lemma_mod_mul_vanish(b, mul_(sub_(a, d), mul_(mod_(a, m), c)), m);
		cong_mul_(mul_(b, mod_(b, m)), mod_(mul_(c, a), m), mul_(b, mod_(add_(b, mul_(mul_(sub_(a, d), mul_(mod_(a, m), c)), m)), m)), mod_(mul_(c, a), m));
		lemma_eq_ref(b);
		cong_mul_(b, mod_(b, m), b, mod_(add_(b, mul_(mul_(sub_(a, d), mul_(mod_(a, m), c)), m)), m));
		lemma_eq_ref(mod_(mul_(c, a), m));
	}
	let temp_79_0 = (mul_((add_(c, b)), (mul_(a, d))));
	let temp_79_1 = (mul_((mul_((add_(c, b)), a)), d));
	assert(eq_(temp_79_0, temp_79_1)) by {
		lemma_mul_assoc(add_(c, b), a, d);
	}
	let temp_80_0 = (sub_((mod_((mul_(d, b)), m)), (mod_((mul_(c, c)), m))));
	let temp_80_1 = (sub_((mod_((mul_(d, b)), m)), (mod_((mul_(c, c)), m))));
	assert(eq_(temp_80_0, temp_80_1)) by {
		lemma_eq_ref(temp_80_0);
	}
	let temp_81_0 = (mul_((mul_(b, d)), (mul_(c, b))));
	let temp_81_1 = (mul_((mul_(d, b)), (mul_(c, b))));
	assert(eq_(temp_81_0, temp_81_1)) by {
		cong_mul_(mul_(b, d), mul_(c, b), mul_(d, b), mul_(c, b));
		lemma_mul_comm(b, d);
		lemma_eq_ref(mul_(c, b));
	}
	let temp_82_0 = (mul_((mul_(a, d)), (mul_(d, c))));
	let temp_82_1 = (mul_((mul_(d, c)), (mul_(a, d))));
	assert(eq_(temp_82_0, temp_82_1)) by {
		lemma_mul_comm(mul_(a, d), mul_(d, c));
	}
	let temp_83_0 = (mul_((mul_(d, a)), (mul_(c, (mod_(d, m))))));
	let temp_83_1 = (mul_(d, (mul_(a, (mul_(c, (mod_(d, m))))))));
	assert(eq_(temp_83_0, temp_83_1)) by {
		lemma_mul_assoc(d, a, mul_(c, mod_(d, m)));
		lemma_eq_sym(temp_83_1, temp_83_0);
	}
	let temp_84_0 = (mod_((sub_((mul_(b, (mod_(c, m)))), (mul_(c, (mod_(b, m)))))), m));
	let temp_84_1 = (mod_((sub_((mul_(b, (mod_(c, m)))), (mul_((mod_(b, m)), c)))), m));
	assert(eq_(temp_84_0, temp_84_1)) by {
		lemma_mul_comm(c, mod_(b, m));
		cong_mod_(sub_(mul_(b, mod_(c, m)), mul_(c, mod_(b, m))), m, sub_(mul_(b, mod_(c, m)), mul_(mod_(b, m), c)), m);
		lemma_eq_ref(m);
		lemma_eq_ref(mul_(b, mod_(c, m)));
		cong_sub_(mul_(b, mod_(c, m)), mul_(c, mod_(b, m)), mul_(b, mod_(c, m)), mul_(mod_(b, m), c));
	}
	let temp_85_0 = (mul_((mul_(b, a)), (mul_(b, (mod_(b, m))))));
	let temp_85_1 = (mul_((mul_((mul_(b, a)), b)), (mod_(b, m))));
	assert(eq_(temp_85_0, temp_85_1)) by {
		lemma_mul_assoc(mul_(b, a), b, mod_(b, m));
	}
	let temp_86_0 = (mul_((add_(d, d)), (mul_(b, d))));
	let temp_86_1 = (mul_((add_(d, d)), (mul_(b, d))));
	assert(eq_(temp_86_0, temp_86_1)) by {
		lemma_eq_ref(temp_86_0);
	}
	let temp_87_0 = (mul_((add_(b, d)), (mul_(d, (mod_(d, m))))));
	let temp_87_1 = (mul_((mul_(d, (mod_(d, m)))), (add_(b, d))));
	assert(eq_(temp_87_0, temp_87_1)) by {
		lemma_mul_comm(add_(b, d), mul_(d, mod_(d, m)));
	}
	let temp_88_0 = (mul_((mul_(d, a)), (mod_((mul_(b, (mod_(d, m)))), m))));
	let temp_88_1 = (mul_((mul_(d, a)), (mod_((mod_((mul_(d, b)), m)), m))));
	assert(eq_(temp_88_0, temp_88_1)) by {
		lemma_mod_mul_noop(d, b, m);
		cong_mul_(mul_(d, a), mod_(mul_(b, mod_(d, m)), m), mul_(d, a), mod_(mod_(mul_(d, b), m), m));
		lemma_eq_ref(mul_(d, a));
		lemma_eq_sym(mod_(mod_(mul_(d, b), m), m), mod_(mul_(b, mod_(d, m)), m));
	}
	let temp_89_0 = (add_((mul_(d, b)), (mod_((mul_(d, c)), m))));
	let temp_89_1 = (add_((mul_(d, b)), (mod_((sub_((mul_(d, c)), (mul_((mul_((mul_(b, c)), (mul_(a, c)))), m)))), m))));
	assert(eq_(temp_89_0, temp_89_1)) by {
		lemma_mod_mul_vanish(mul_(d, c), mul_(mul_(b, c), mul_(a, c)), m);
		cong_add_(mul_(d, b), mod_(mul_(d, c), m), mul_(d, b), mod_(sub_(mul_(d, c), mul_(mul_(mul_(b, c), mul_(a, c)), m)), m));
		lemma_eq_ref(mul_(d, b));
	}
	let temp_90_0 = (mul_((mul_(a, b)), (mul_(c, d))));
	let temp_90_1 = (mul_(a, (mul_(b, (mul_(c, d))))));
	assert(eq_(temp_90_0, temp_90_1)) by {
		lemma_eq_sym(temp_90_1, temp_90_0);
		lemma_mul_assoc(a, b, mul_(c, d));
	}
	let temp_91_0 = (add_((mul_(d, a)), (mul_(d, c))));
	let temp_91_1 = (add_((mul_(d, c)), (mul_(d, a))));
	assert(eq_(temp_91_0, temp_91_1)) by {
		lemma_add_comm(mul_(d, a), mul_(d, c));
	}
	let temp_92_0 = (mul_((mul_(d, b)), (mul_(a, c))));
	let temp_92_1 = (mul_((mul_(d, b)), (mul_(c, a))));
	assert(eq_(temp_92_0, temp_92_1)) by {
		cong_mul_(mul_(d, b), mul_(a, c), mul_(d, b), mul_(c, a));
		lemma_mul_comm(a, c);
		lemma_eq_ref(mul_(d, b));
	}
	let temp_93_0 = (mul_((mul_(d, c)), (mul_(d, b))));
	let temp_93_1 = (mul_((mul_(c, d)), (mul_(d, b))));
	assert(eq_(temp_93_0, temp_93_1)) by {
		cong_mul_(mul_(d, c), mul_(d, b), mul_(c, d), mul_(d, b));
		lemma_mul_comm(d, c);
		lemma_eq_ref(mul_(d, b));
	}
	let temp_94_0 = (mul_((mul_(a, d)), (mul_(c, c))));
	let temp_94_1 = (mul_((mul_(c, c)), (mul_(a, d))));
	assert(eq_(temp_94_0, temp_94_1)) by {
		lemma_mul_comm(mul_(a, d), mul_(c, c));
	}
	let temp_95_0 = (mod_((mul_((sub_(d, c)), (mul_(c, a)))), m));
	let temp_95_1 = (mod_((sub_((mul_((sub_(d, c)), (mul_(c, a)))), (mul_((mul_((mul_(b, (mod_(b, m)))), (mul_(c, a)))), m)))), m));
	assert(eq_(temp_95_0, temp_95_1)) by {
		lemma_mod_mul_vanish(mul_(sub_(d, c), mul_(c, a)), mul_(mul_(b, mod_(b, m)), mul_(c, a)), m);
	}
	let temp_96_0 = (mul_((mul_(d, c)), (mul_(a, c))));
	let temp_96_1 = (mul_(d, (mul_(c, (mul_(a, c))))));
	assert(eq_(temp_96_0, temp_96_1)) by {
		lemma_eq_sym(temp_96_1, temp_96_0);
		lemma_mul_assoc(d, c, mul_(a, c));
	}

}

} // verus!