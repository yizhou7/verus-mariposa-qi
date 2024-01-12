use builtin_macros::*;
// use builtin::*;
mod nl_basics;
use crate::nl_basics::*;
verus! {

pub proof fn free_0(a: Elem, b: Elem, c: Elem, d: Elem, m: Elem)
{
	let temp_0_0 = (add_((mod_((mul_(d, b)), m)), (mul_(d, a))));
	let temp_0_1 = (add_((mul_(d, a)), (mod_((mul_(d, b)), m))));
	assert(eq_(temp_0_0, temp_0_1)) by {
		lemma_add_comm(mod_(mul_(d, b), m), mul_(d, a));
	}
	let temp_1_0 = (mod_((mul_((mul_((mod_(a, m)), b)), (sub_(d, c)))), m));
	let temp_1_1 = (mod_((mul_((mul_(b, (mod_(a, m)))), (sub_(d, c)))), m));
	assert(eq_(temp_1_0, temp_1_1)) by {
		lemma_mul_comm(mod_(a, m), b);
		cong_mod_(mul_(mul_(mod_(a, m), b), sub_(d, c)), m, mul_(mul_(b, mod_(a, m)), sub_(d, c)), m);
		cong_mul_(mul_(mod_(a, m), b), sub_(d, c), mul_(b, mod_(a, m)), sub_(d, c));
		lemma_eq_ref(sub_(d, c));
		lemma_eq_ref(m);
	}
	let temp_2_0 = (mul_((mod_((mul_(b, a)), m)), (add_(b, d))));
	let temp_2_1 = (mul_((add_(b, d)), (mod_((mul_(b, a)), m))));
	assert(eq_(temp_2_0, temp_2_1)) by {
		lemma_mul_comm(mod_(mul_(b, a), m), add_(b, d));
	}
	let temp_3_0 = (sub_((mul_(b, b)), (mul_(b, b))));
	let temp_3_1 = (sub_((mul_(b, b)), (mul_(b, b))));
	assert(eq_(temp_3_0, temp_3_1)) by {
		lemma_eq_ref(temp_3_0);
	}
	let temp_4_0 = (mul_((mul_(a, b)), (mod_((mul_(a, d)), m))));
	let temp_4_1 = (mul_((mul_(a, b)), (mod_((add_((mul_((mul_((sub_(a, (mod_(c, m)))), (mul_(d, c)))), m)), (mul_(a, d)))), m))));
	assert(eq_(temp_4_0, temp_4_1)) by {
		lemma_mod_mul_vanish(mul_(a, d), mul_(sub_(a, mod_(c, m)), mul_(d, c)), m);
		cong_mul_(mul_(a, b), mod_(mul_(a, d), m), mul_(a, b), mod_(add_(mul_(mul_(sub_(a, mod_(c, m)), mul_(d, c)), m), mul_(a, d)), m));
		lemma_eq_ref(mul_(a, b));
	}
	let temp_5_0 = (mul_((sub_(d, (mod_(a, m)))), (mul_((mod_(a, m)), c))));
	let temp_5_1 = (sub_((mul_(d, (mul_((mod_(a, m)), c)))), (mul_((mod_(a, m)), (mul_((mod_(a, m)), c))))));
	assert(eq_(temp_5_0, temp_5_1)) by {
		lemma_mul_dist(mul_(mod_(a, m), c), d, mod_(a, m));
	}
	let temp_6_0 = (add_((mul_(c, a)), (mul_(a, c))));
	let temp_6_1 = (add_((mul_(a, c)), (mul_(a, c))));
	assert(eq_(temp_6_0, temp_6_1)) by {
		cong_add_(mul_(c, a), mul_(a, c), mul_(a, c), mul_(a, c));
		lemma_mul_comm(c, a);
		lemma_eq_ref(mul_(a, c));
	}
	let temp_7_0 = (mul_((add_(d, as_elem(5))), (sub_(d, d))));
	let temp_7_1 = (add_((mul_(d, (sub_(d, d)))), (mul_(as_elem(5), (sub_(d, d))))));
	assert(eq_(temp_7_0, temp_7_1)) by {
		lemma_mul_dist(d, as_elem(5), sub_(d, d));
	}
	let temp_8_0 = (mul_((add_(b, d)), (mul_(d, as_elem(90)))));
	let temp_8_1 = (add_((mul_(b, (mul_(d, as_elem(90))))), (mul_(d, (mul_(d, as_elem(90)))))));
	assert(eq_(temp_8_0, temp_8_1)) by {
		lemma_mul_dist(b, d, mul_(d, as_elem(90)));
	}
	let temp_9_0 = (mod_((mul_((mul_(c, d)), (mod_((add_(c, c)), m)))), m));
	let temp_9_1 = (mod_((mul_((mod_((add_(c, c)), m)), (mul_(c, d)))), m));
	assert(eq_(temp_9_0, temp_9_1)) by {
		lemma_mul_comm(mul_(c, d), mod_(add_(c, c), m));
		cong_mod_(mul_(mul_(c, d), mod_(add_(c, c), m)), m, mul_(mod_(add_(c, c), m), mul_(c, d)), m);
		lemma_eq_ref(m);
	}
	let temp_10_0 = (mul_((add_(as_elem(59), a)), (mul_(d, d))));
	let temp_10_1 = (mul_((mul_((add_(as_elem(59), a)), d)), d));
	assert(eq_(temp_10_0, temp_10_1)) by {
		lemma_mul_assoc(add_(as_elem(59), a), d, d);
	}
	let temp_11_0 = (mul_((mul_(a, c)), (mul_(as_elem(59), c))));
	let temp_11_1 = (mul_((mul_(c, a)), (mul_(as_elem(59), c))));
	assert(eq_(temp_11_0, temp_11_1)) by {
		cong_mul_(mul_(a, c), mul_(as_elem(59), c), mul_(c, a), mul_(as_elem(59), c));
		lemma_mul_comm(a, c);
		lemma_eq_ref(mul_(as_elem(59), c));
	}
	let temp_12_0 = (mul_((mul_(d, c)), (mul_(a, c))));
	let temp_12_1 = (mul_((mul_(c, d)), (mul_(a, c))));
	assert(eq_(temp_12_0, temp_12_1)) by {
		cong_mul_(mul_(d, c), mul_(a, c), mul_(c, d), mul_(a, c));
		lemma_mul_comm(d, c);
		lemma_eq_ref(mul_(a, c));
	}
	let temp_13_0 = (mul_((mul_(d, b)), (mul_(c, (mod_(d, m))))));
	let temp_13_1 = (mul_((mul_(c, (mod_(d, m)))), (mul_(d, b))));
	assert(eq_(temp_13_0, temp_13_1)) by {
		lemma_mul_comm(mul_(d, b), mul_(c, mod_(d, m)));
	}
	let temp_14_0 = (mul_((mul_(c, a)), (mul_(d, a))));
	let temp_14_1 = (mul_((mul_(a, c)), (mul_(d, a))));
	assert(eq_(temp_14_0, temp_14_1)) by {
		cong_mul_(mul_(c, a), mul_(d, a), mul_(a, c), mul_(d, a));
		lemma_mul_comm(c, a);
		lemma_eq_ref(mul_(d, a));
	}
	let temp_15_0 = (add_((mul_(c, a)), (mod_((mul_(a, b)), m))));
	let temp_15_1 = (add_((mul_(c, a)), (mod_((add_((mul_((mul_((mul_(c, b)), (mul_(b, c)))), m)), (mul_(a, b)))), m))));
	assert(eq_(temp_15_0, temp_15_1)) by {
		lemma_mod_mul_vanish(mul_(a, b), mul_(mul_(c, b), mul_(b, c)), m);
		cong_add_(mul_(c, a), mod_(mul_(a, b), m), mul_(c, a), mod_(add_(mul_(mul_(mul_(c, b), mul_(b, c)), m), mul_(a, b)), m));
		lemma_eq_ref(mul_(c, a));
	}
	let temp_16_0 = (mul_((mul_(d, (mod_(a, m)))), (add_(b, b))));
	let temp_16_1 = (mul_((mul_(d, (mod_(a, m)))), (add_(b, b))));
	assert(eq_(temp_16_0, temp_16_1)) by {
		lemma_eq_ref(temp_16_0);
	}
	let temp_17_0 = (mul_((mul_(d, a)), (add_(b, a))));
	let temp_17_1 = (add_((mul_((mul_(d, a)), b)), (mul_((mul_(d, a)), a))));
	assert(eq_(temp_17_0, temp_17_1)) by {
		lemma_mul_dist(mul_(d, a), b, a);
	}
	let temp_18_0 = (add_((mul_(b, b)), (mul_(b, c))));
	let temp_18_1 = (add_((mul_(b, b)), (mul_(b, c))));
	assert(eq_(temp_18_0, temp_18_1)) by {
		lemma_eq_ref(temp_18_0);
	}
	let temp_19_0 = (mul_((mod_((mul_(a, c)), m)), (mul_(b, a))));
	let temp_19_1 = (mul_((mul_((mod_((mul_(a, c)), m)), b)), a));
	assert(eq_(temp_19_0, temp_19_1)) by {
		lemma_mul_assoc(mod_(mul_(a, c), m), b, a);
	}
	let temp_20_0 = (mul_((mul_(b, b)), (add_(d, c))));
	let temp_20_1 = (mul_((add_(d, c)), (mul_(b, b))));
	assert(eq_(temp_20_0, temp_20_1)) by {
		lemma_mul_comm(mul_(b, b), add_(d, c));
	}
	let temp_21_0 = (mul_((mul_(d, b)), (mul_(a, d))));
	let temp_21_1 = (mul_(d, (mul_(b, (mul_(a, d))))));
	assert(eq_(temp_21_0, temp_21_1)) by {
		lemma_eq_sym(temp_21_1, temp_21_0);
		lemma_mul_assoc(d, b, mul_(a, d));
	}
	let temp_22_0 = (mul_((mul_(b, a)), (mul_(b, d))));
	let temp_22_1 = (mul_(b, (mul_(a, (mul_(b, d))))));
	assert(eq_(temp_22_0, temp_22_1)) by {
		lemma_eq_sym(temp_22_1, temp_22_0);
		lemma_mul_assoc(b, a, mul_(b, d));
	}
	let temp_23_0 = (mul_((add_(d, b)), (mul_(b, c))));
	let temp_23_1 = (mul_((mul_((add_(d, b)), b)), c));
	assert(eq_(temp_23_0, temp_23_1)) by {
		lemma_mul_assoc(add_(d, b), b, c);
	}
	let temp_24_0 = (mod_((mul_((mul_(c, (mod_(b, m)))), (mul_(d, a)))), m));
	let temp_24_1 = (mod_((mul_((mul_((mod_(b, m)), c)), (mul_(d, a)))), m));
	assert(eq_(temp_24_0, temp_24_1)) by {
		lemma_mul_comm(c, mod_(b, m));
		cong_mod_(mul_(mul_(c, mod_(b, m)), mul_(d, a)), m, mul_(mul_(mod_(b, m), c), mul_(d, a)), m);
		lemma_eq_ref(mul_(d, a));
		lemma_eq_ref(m);
		cong_mul_(mul_(c, mod_(b, m)), mul_(d, a), mul_(mod_(b, m), c), mul_(d, a));
	}
	let temp_25_0 = (add_((mul_(d, b)), (mul_((mod_(a, m)), a))));
	let temp_25_1 = (add_((mul_(d, b)), (mul_((mod_((add_((mul_((mul_((mul_(b, d)), (mul_(a, d)))), m)), a)), m)), a))));
	assert(eq_(temp_25_0, temp_25_1)) by {
		lemma_mod_mul_vanish(a, mul_(mul_(b, d), mul_(a, d)), m);
		cong_add_(mul_(d, b), mul_(mod_(a, m), a), mul_(d, b), mul_(mod_(add_(mul_(mul_(mul_(b, d), mul_(a, d)), m), a), m), a));
		lemma_eq_ref(a);
		lemma_eq_ref(mul_(d, b));
		cong_mul_(mod_(a, m), a, mod_(add_(mul_(mul_(mul_(b, d), mul_(a, d)), m), a), m), a);
	}
	let temp_26_0 = (mod_((mul_((mul_(b, c)), (mul_(b, c)))), m));
	let temp_26_1 = (mod_((sub_((mul_((mul_(b, c)), (mul_(b, c)))), (mul_((mul_((mul_(a, c)), (mul_((mod_(d, m)), d)))), m)))), m));
	assert(eq_(temp_26_0, temp_26_1)) by {
		lemma_mod_mul_vanish(mul_(mul_(b, c), mul_(b, c)), mul_(mul_(a, c), mul_(mod_(d, m), d)), m);
	}
	let temp_27_0 = (mul_((mul_(c, (mod_(b, m)))), (mul_(c, a))));
	let temp_27_1 = (mul_((mul_((mod_(b, m)), c)), (mul_(c, a))));
	assert(eq_(temp_27_0, temp_27_1)) by {
		lemma_mul_comm(c, mod_(b, m));
		cong_mul_(mul_(c, mod_(b, m)), mul_(c, a), mul_(mod_(b, m), c), mul_(c, a));
		lemma_eq_ref(mul_(c, a));
	}
	let temp_28_0 = (mul_((mul_((mod_(d, m)), c)), (sub_(d, a))));
	let temp_28_1 = (mul_((mul_(c, (mod_(d, m)))), (sub_(d, a))));
	assert(eq_(temp_28_0, temp_28_1)) by {
		lemma_mul_comm(mod_(d, m), c);
		cong_mul_(mul_(mod_(d, m), c), sub_(d, a), mul_(c, mod_(d, m)), sub_(d, a));
		lemma_eq_ref(sub_(d, a));
	}
	let temp_29_0 = (mul_((mul_(c, c)), (mul_(c, (mod_(c, m))))));
	let temp_29_1 = (mul_((mul_(c, c)), (mul_(c, (mod_(c, m))))));
	assert(eq_(temp_29_0, temp_29_1)) by {
		lemma_eq_ref(temp_29_0);
	}
	let temp_30_0 = (sub_((mul_(d, a)), (mul_(a, b))));
	let temp_30_1 = (sub_((mul_(d, a)), (mul_(b, a))));
	assert(eq_(temp_30_0, temp_30_1)) by {
		lemma_eq_ref(mul_(d, a));
		cong_sub_(mul_(d, a), mul_(a, b), mul_(d, a), mul_(b, a));
		lemma_mul_comm(a, b);
	}
	let temp_31_0 = (mul_((mul_(c, b)), (mul_(b, c))));
	let temp_31_1 = (mul_((mul_((mul_(c, b)), b)), c));
	assert(eq_(temp_31_0, temp_31_1)) by {
		lemma_mul_assoc(mul_(c, b), b, c);
	}
	let temp_32_0 = (mul_((mul_(b, d)), (mul_(b, (mod_(d, m))))));
	let temp_32_1 = (mul_((mul_(b, (mod_(d, m)))), (mul_(b, d))));
	assert(eq_(temp_32_0, temp_32_1)) by {
		lemma_mul_comm(mul_(b, d), mul_(b, mod_(d, m)));
	}
	let temp_33_0 = (mul_((mod_((sub_(c, d)), m)), (mul_(b, (mod_(a, m))))));
	let temp_33_1 = (mul_((mod_((sub_(c, d)), m)), (mul_(b, (mod_((add_(a, (mul_((mul_((mul_(a, c)), (mul_((mod_(c, m)), b)))), m)))), m))))));
	assert(eq_(temp_33_0, temp_33_1)) by {
		lemma_mod_mul_vanish(a, mul_(mul_(a, c), mul_(mod_(c, m), b)), m);
		cong_mul_(mod_(sub_(c, d), m), mul_(b, mod_(a, m)), mod_(sub_(c, d), m), mul_(b, mod_(add_(a, mul_(mul_(mul_(a, c), mul_(mod_(c, m), b)), m)), m)));
		cong_mul_(b, mod_(a, m), b, mod_(add_(a, mul_(mul_(mul_(a, c), mul_(mod_(c, m), b)), m)), m));
		lemma_eq_ref(b);
		lemma_eq_ref(mod_(sub_(c, d), m));
	}
	let temp_34_0 = (mul_((sub_(d, a)), (mul_(c, a))));
	let temp_34_1 = (mul_((mul_(c, a)), (sub_(d, a))));
	assert(eq_(temp_34_0, temp_34_1)) by {
		lemma_mul_comm(sub_(d, a), mul_(c, a));
	}
	let temp_35_0 = (sub_((mul_(d, d)), (mul_(a, a))));
	let temp_35_1 = (sub_((mul_(d, d)), (mul_(a, a))));
	assert(eq_(temp_35_0, temp_35_1)) by {
		lemma_eq_ref(temp_35_0);
	}
	let temp_36_0 = (mul_((mul_(a, c)), (mul_(b, a))));
	let temp_36_1 = (mul_((mul_(a, c)), (mul_(a, b))));
	assert(eq_(temp_36_0, temp_36_1)) by {
		cong_mul_(mul_(a, c), mul_(b, a), mul_(a, c), mul_(a, b));
		lemma_mul_comm(b, a);
		lemma_eq_ref(mul_(a, c));
	}
	let temp_37_0 = (mul_((mod_((mul_(b, (mod_(a, m)))), m)), (mul_(a, c))));
	let temp_37_1 = (mul_((mod_((mul_((mod_(a, m)), b)), m)), (mul_(a, c))));
	assert(eq_(temp_37_0, temp_37_1)) by {
		lemma_mul_comm(b, mod_(a, m));
		cong_mul_(mod_(mul_(b, mod_(a, m)), m), mul_(a, c), mod_(mul_(mod_(a, m), b), m), mul_(a, c));
		lemma_eq_ref(m);
		cong_mod_(mul_(b, mod_(a, m)), m, mul_(mod_(a, m), b), m);
		lemma_eq_ref(mul_(a, c));
	}
	let temp_38_0 = (mul_((add_((mod_(c, m)), a)), (sub_(d, (mod_(c, m))))));
	let temp_38_1 = (add_((mul_((mod_(c, m)), (sub_(d, (mod_(c, m)))))), (mul_(a, (sub_(d, (mod_(c, m))))))));
	assert(eq_(temp_38_0, temp_38_1)) by {
		lemma_mul_dist(mod_(c, m), a, sub_(d, mod_(c, m)));
	}
	let temp_39_0 = (mul_((mul_((mod_(a, m)), a)), (mul_(d, c))));
	let temp_39_1 = (mul_((mul_((mod_((add_((mul_((mul_((mul_(a, d)), (mod_((mul_(c, d)), m)))), m)), a)), m)), a)), (mul_(d, c))));
	assert(eq_(temp_39_0, temp_39_1)) by {
		lemma_mod_mul_vanish(a, mul_(mul_(a, d), mod_(mul_(c, d), m)), m);
		cong_mul_(mul_(mod_(a, m), a), mul_(d, c), mul_(mod_(add_(mul_(mul_(mul_(a, d), mod_(mul_(c, d), m)), m), a), m), a), mul_(d, c));
		lemma_eq_ref(a);
		lemma_eq_ref(mul_(d, c));
		cong_mul_(mod_(a, m), a, mod_(add_(mul_(mul_(mul_(a, d), mod_(mul_(c, d), m)), m), a), m), a);
	}
	let temp_40_0 = (mul_((mul_(b, d)), (mul_(c, (mod_(b, m))))));
	let temp_40_1 = (mul_((mul_(c, (mod_(b, m)))), (mul_(b, d))));
	assert(eq_(temp_40_0, temp_40_1)) by {
		lemma_mul_comm(mul_(b, d), mul_(c, mod_(b, m)));
	}
	let temp_41_0 = (mul_((mul_(b, c)), (mul_(c, b))));
	let temp_41_1 = (mul_(b, (mul_(c, (mul_(c, b))))));
	assert(eq_(temp_41_0, temp_41_1)) by {
		lemma_eq_sym(temp_41_1, temp_41_0);
		lemma_mul_assoc(b, c, mul_(c, b));
	}
	let temp_42_0 = (mul_((mod_((mul_(c, b)), m)), (mod_(a, m))));
	let temp_42_1 = (mul_((mod_(a, m)), (mod_((mul_(c, b)), m))));
	assert(eq_(temp_42_0, temp_42_1)) by {
		lemma_mul_comm(mod_(mul_(c, b), m), mod_(a, m));
	}
	let temp_43_0 = (mul_((mod_((mul_(b, d)), m)), d));
	let temp_43_1 = (mul_((mod_((mul_(d, b)), m)), d));
	assert(eq_(temp_43_0, temp_43_1)) by {
		cong_mul_(mod_(mul_(b, d), m), d, mod_(mul_(d, b), m), d);
		lemma_mul_comm(b, d);
		lemma_eq_ref(d);
		cong_mod_(mul_(b, d), m, mul_(d, b), m);
		lemma_eq_ref(m);
	}
	let temp_44_0 = (add_((mul_(c, c)), (mul_(c, a))));
	let temp_44_1 = (add_((mul_(c, c)), (mul_(a, c))));
	assert(eq_(temp_44_0, temp_44_1)) by {
		cong_add_(mul_(c, c), mul_(c, a), mul_(c, c), mul_(a, c));
		lemma_mul_comm(c, a);
		lemma_eq_ref(mul_(c, c));
	}
	let temp_45_0 = (mul_((mul_(a, as_elem(68))), (mul_(c, (mod_(b, m))))));
	let temp_45_1 = (mul_((mul_(a, as_elem(68))), (mul_(c, (mod_((add_(b, (mul_((mul_((mul_(b, b)), b)), m)))), m))))));
	assert(eq_(temp_45_0, temp_45_1)) by {
		lemma_eq_ref(mul_(a, as_elem(68)));
		lemma_mod_mul_vanish(b, mul_(mul_(b, b), b), m);
		cong_mul_(mul_(a, as_elem(68)), mul_(c, mod_(b, m)), mul_(a, as_elem(68)), mul_(c, mod_(add_(b, mul_(mul_(mul_(b, b), b), m)), m)));
		lemma_eq_ref(c);
		cong_mul_(c, mod_(b, m), c, mod_(add_(b, mul_(mul_(mul_(b, b), b), m)), m));
	}
	let temp_46_0 = (mul_((mul_(d, c)), (mul_(b, d))));
	let temp_46_1 = (mul_((mul_(b, d)), (mul_(d, c))));
	assert(eq_(temp_46_0, temp_46_1)) by {
		lemma_mul_comm(mul_(d, c), mul_(b, d));
	}
	let temp_47_0 = (sub_((mul_(c, c)), (mul_(c, c))));
	let temp_47_1 = (sub_((mul_(c, c)), (mul_(c, c))));
	assert(eq_(temp_47_0, temp_47_1)) by {
		lemma_eq_ref(temp_47_0);
	}
	let temp_48_0 = (mul_((mul_(d, d)), (mul_(as_elem(11), c))));
	let temp_48_1 = (mul_((mul_(d, d)), (mul_(c, as_elem(11)))));
	assert(eq_(temp_48_0, temp_48_1)) by {
		cong_mul_(mul_(d, d), mul_(as_elem(11), c), mul_(d, d), mul_(c, as_elem(11)));
		lemma_mul_comm(d, d);
		lemma_mul_comm(as_elem(11), c);
	}
	let temp_49_0 = (mul_((mod_((mul_(as_elem(100), d)), m)), (mul_((mod_(b, m)), a))));
	let temp_49_1 = (mul_((mod_((mul_(as_elem(100), d)), m)), (mul_((mod_((sub_(b, (mul_((add_((mul_(a, a)), (sub_(b, b)))), m)))), m)), a))));
	assert(eq_(temp_49_0, temp_49_1)) by {
		cong_mul_(mod_(mul_(as_elem(100), d), m), mul_(mod_(b, m), a), mod_(mul_(as_elem(100), d), m), mul_(mod_(sub_(b, mul_(add_(mul_(a, a), sub_(b, b)), m)), m), a));
		lemma_mod_mul_vanish(b, add_(mul_(a, a), sub_(b, b)), m);
		lemma_eq_ref(mod_(mul_(as_elem(100), d), m));
		lemma_eq_ref(a);
		cong_mul_(mod_(b, m), a, mod_(sub_(b, mul_(add_(mul_(a, a), sub_(b, b)), m)), m), a);
	}
	let temp_50_0 = (add_((mul_(c, c)), (add_(a, a))));
	let temp_50_1 = (add_((add_(a, a)), (mul_(c, c))));
	assert(eq_(temp_50_0, temp_50_1)) by {
		lemma_add_comm(mul_(c, c), add_(a, a));
	}
	let temp_51_0 = (mul_((mod_((mul_(d, a)), m)), (mul_(d, a))));
	let temp_51_1 = (mul_((mul_((mod_((mul_(d, a)), m)), d)), a));
	assert(eq_(temp_51_0, temp_51_1)) by {
		lemma_mul_assoc(mod_(mul_(d, a), m), d, a);
	}
	let temp_52_0 = (mul_((mul_(b, c)), (mul_(c, c))));
	let temp_52_1 = (mul_((mul_(c, c)), (mul_(b, c))));
	assert(eq_(temp_52_0, temp_52_1)) by {
		lemma_mul_comm(mul_(b, c), mul_(c, c));
	}
	let temp_53_0 = (mul_((mod_((add_(c, c)), m)), (mul_(d, c))));
	let temp_53_1 = (mul_((mul_((mod_((add_(c, c)), m)), d)), c));
	assert(eq_(temp_53_0, temp_53_1)) by {
		lemma_mul_assoc(mod_(add_(c, c), m), d, c);
	}
	let temp_54_0 = (mul_((mul_(a, b)), (mul_(a, a))));
	let temp_54_1 = (mul_((mul_((mul_(a, b)), a)), a));
	assert(eq_(temp_54_0, temp_54_1)) by {
		lemma_mul_assoc(mul_(a, b), a, a);
	}
	let temp_55_0 = (mul_((mul_(d, c)), (mul_(a, a))));
	let temp_55_1 = (mul_(d, (mul_(c, (mul_(a, a))))));
	assert(eq_(temp_55_0, temp_55_1)) by {
		lemma_eq_sym(temp_55_1, temp_55_0);
		lemma_mul_assoc(d, c, mul_(a, a));
	}
	let temp_56_0 = (mul_((add_(c, d)), (mul_(a, b))));
	let temp_56_1 = (mul_((mul_(a, b)), (add_(c, d))));
	assert(eq_(temp_56_0, temp_56_1)) by {
		lemma_mul_comm(add_(c, d), mul_(a, b));
	}
	let temp_57_0 = (mul_((mul_(c, a)), (mul_(b, c))));
	let temp_57_1 = (mul_((mul_((mul_(c, a)), b)), c));
	assert(eq_(temp_57_0, temp_57_1)) by {
		lemma_mul_assoc(mul_(c, a), b, c);
	}
	let temp_58_0 = (mul_((mul_(d, a)), (mul_(d, d))));
	let temp_58_1 = (mul_(d, (mul_(a, (mul_(d, d))))));
	assert(eq_(temp_58_0, temp_58_1)) by {
		lemma_eq_sym(temp_58_1, temp_58_0);
		lemma_mul_assoc(d, a, mul_(d, d));
	}
	let temp_59_0 = (mul_((mul_(b, d)), (mod_((mul_(a, (mod_(b, m)))), m))));
	let temp_59_1 = (mul_((mod_((mul_(a, (mod_(b, m)))), m)), (mul_(b, d))));
	assert(eq_(temp_59_0, temp_59_1)) by {
		lemma_mul_comm(mul_(b, d), mod_(mul_(a, mod_(b, m)), m));
	}
	let temp_60_0 = (mul_((mul_(d, d)), (mod_((mul_((mod_(c, m)), d)), m))));
	let temp_60_1 = (mul_(d, (mul_(d, (mod_((mul_((mod_(c, m)), d)), m))))));
	assert(eq_(temp_60_0, temp_60_1)) by {
		lemma_mul_assoc(d, d, mod_(mul_(mod_(c, m), d), m));
		lemma_eq_sym(temp_60_1, temp_60_0);
	}
	let temp_61_0 = (mul_((mod_((mul_(b, (mod_(c, m)))), m)), (mul_(a, c))));
	let temp_61_1 = (mul_((mul_((mod_((mul_(b, (mod_(c, m)))), m)), a)), c));
	assert(eq_(temp_61_0, temp_61_1)) by {
		lemma_mul_assoc(mod_(mul_(b, mod_(c, m)), m), a, c);
	}
	let temp_62_0 = (sub_((mul_(c, c)), (add_(a, a))));
	let temp_62_1 = (sub_((mul_(c, c)), (add_(a, a))));
	assert(eq_(temp_62_0, temp_62_1)) by {
		lemma_eq_ref(temp_62_0);
	}
	let temp_63_0 = (mul_((mod_((mul_((mod_(d, m)), c)), m)), (mul_(d, d))));
	let temp_63_1 = (mul_((mod_((add_((mul_((mul_((mul_(c, (mod_(b, m)))), (mul_(c, a)))), m)), (mul_((mod_(d, m)), c)))), m)), (mul_(d, d))));
	assert(eq_(temp_63_0, temp_63_1)) by {
		lemma_mul_comm(d, d);
		lemma_mod_mul_vanish(mul_(mod_(d, m), c), mul_(mul_(c, mod_(b, m)), mul_(c, a)), m);
		cong_mul_(mod_(mul_(mod_(d, m), c), m), mul_(d, d), mod_(add_(mul_(mul_(mul_(c, mod_(b, m)), mul_(c, a)), m), mul_(mod_(d, m), c)), m), mul_(d, d));
	}
	let temp_64_0 = (mul_((mod_((sub_(c, a)), m)), (mul_(b, c))));
	let temp_64_1 = (mul_((mod_((sub_(c, a)), m)), (mul_(c, b))));
	assert(eq_(temp_64_0, temp_64_1)) by {
		lemma_mul_comm(b, c);
		cong_mul_(mod_(sub_(c, a), m), mul_(b, c), mod_(sub_(c, a), m), mul_(c, b));
		lemma_eq_ref(mod_(sub_(c, a), m));
	}
	let temp_65_0 = (sub_((mul_(d, a)), (mul_((mod_(b, m)), b))));
	let temp_65_1 = (sub_((mul_(d, a)), (mul_((mod_((add_(b, (mul_((mul_((mul_(d, d)), (mul_(a, d)))), m)))), m)), b))));
	assert(eq_(temp_65_0, temp_65_1)) by {
		lemma_mod_mul_vanish(b, mul_(mul_(d, d), mul_(a, d)), m);
		cong_sub_(mul_(d, a), mul_(mod_(b, m), b), mul_(d, a), mul_(mod_(add_(b, mul_(mul_(mul_(d, d), mul_(a, d)), m)), m), b));
		lemma_eq_ref(mul_(d, a));
		cong_mul_(mod_(b, m), b, mod_(add_(b, mul_(mul_(mul_(d, d), mul_(a, d)), m)), m), b);
		lemma_eq_ref(b);
	}
	let temp_66_0 = (mul_((mul_(b, (mod_(a, m)))), (mul_(a, c))));
	let temp_66_1 = (mul_((mul_(a, c)), (mul_(b, (mod_(a, m))))));
	assert(eq_(temp_66_0, temp_66_1)) by {
		lemma_mul_comm(mul_(b, mod_(a, m)), mul_(a, c));
	}
	let temp_67_0 = (add_((sub_(a, a)), (mod_((mul_(a, c)), m))));
	let temp_67_1 = (add_((sub_(a, a)), (mod_((add_((mul_(a, c)), (mul_((mul_((sub_(c, a)), (mul_(d, b)))), m)))), m))));
	assert(eq_(temp_67_0, temp_67_1)) by {
		lemma_mod_mul_vanish(mul_(a, c), mul_(sub_(c, a), mul_(d, b)), m);
		cong_add_(sub_(a, a), mod_(mul_(a, c), m), sub_(a, a), mod_(add_(mul_(a, c), mul_(mul_(sub_(c, a), mul_(d, b)), m)), m));
		lemma_eq_ref(sub_(a, a));
	}
	let temp_68_0 = (mul_((mul_(b, a)), (mul_(d, a))));
	let temp_68_1 = (mul_((mul_(a, b)), (mul_(d, a))));
	assert(eq_(temp_68_0, temp_68_1)) by {
		cong_mul_(mul_(b, a), mul_(d, a), mul_(a, b), mul_(d, a));
		lemma_mul_comm(b, a);
		lemma_eq_ref(mul_(d, a));
	}
	let temp_69_0 = (mul_((mul_(b, a)), (mul_(b, a))));
	let temp_69_1 = (mul_(b, (mul_(a, (mul_(b, a))))));
	assert(eq_(temp_69_0, temp_69_1)) by {
		lemma_eq_sym(temp_69_1, temp_69_0);
		lemma_mul_assoc(b, a, mul_(b, a));
	}
	let temp_70_0 = (mod_((mul_((mul_(d, c)), (mul_(a, (mod_(a, m)))))), m));
	let temp_70_1 = (mod_((mul_((mul_(d, c)), (mul_((mod_(a, m)), a)))), m));
	assert(eq_(temp_70_0, temp_70_1)) by {
		lemma_mul_comm(a, mod_(a, m));
		cong_mod_(mul_(mul_(d, c), mul_(a, mod_(a, m))), m, mul_(mul_(d, c), mul_(mod_(a, m), a)), m);
		lemma_eq_ref(mul_(d, c));
		cong_mul_(mul_(d, c), mul_(a, mod_(a, m)), mul_(d, c), mul_(mod_(a, m), a));
		lemma_eq_ref(m);
	}
	let temp_71_0 = (mul_((mul_(d, c)), (add_(b, a))));
	let temp_71_1 = (add_((mul_((mul_(d, c)), b)), (mul_((mul_(d, c)), a))));
	assert(eq_(temp_71_0, temp_71_1)) by {
		lemma_mul_dist(mul_(d, c), b, a);
	}
	let temp_72_0 = (mul_((mul_(b, a)), (mul_(b, d))));
	let temp_72_1 = (mul_((mul_(b, d)), (mul_(b, a))));
	assert(eq_(temp_72_0, temp_72_1)) by {
		lemma_mul_comm(mul_(b, a), mul_(b, d));
	}
	let temp_73_0 = (mul_((sub_(a, (mod_(c, m)))), (mul_(b, (mod_(d, m))))));
	let temp_73_1 = (mul_((mul_((sub_(a, (mod_(c, m)))), b)), (mod_(d, m))));
	assert(eq_(temp_73_0, temp_73_1)) by {
		lemma_mul_assoc(sub_(a, mod_(c, m)), b, mod_(d, m));
	}
	let temp_74_0 = (mul_((mul_(a, a)), (mul_(a, b))));
	let temp_74_1 = (mul_((mul_(a, a)), (mul_(b, a))));
	assert(eq_(temp_74_0, temp_74_1)) by {
		cong_mul_(mul_(a, a), mul_(a, b), mul_(a, a), mul_(b, a));
		lemma_mul_comm(a, a);
		lemma_mul_comm(a, b);
	}
	let temp_75_0 = (mul_((sub_(a, a)), (mul_((mod_(b, m)), c))));
	let temp_75_1 = (sub_((mul_(a, (mul_((mod_(b, m)), c)))), (mul_(a, (mul_((mod_(b, m)), c))))));
	assert(eq_(temp_75_0, temp_75_1)) by {
		lemma_mul_dist(mul_(mod_(b, m), c), a, a);
	}
	let temp_76_0 = (sub_((mul_(a, a)), (mul_(c, d))));
	let temp_76_1 = (sub_((mul_(a, a)), (mul_(d, c))));
	assert(eq_(temp_76_0, temp_76_1)) by {
		cong_sub_(mul_(a, a), mul_(c, d), mul_(a, a), mul_(d, c));
		lemma_mul_comm(c, d);
		lemma_eq_ref(mul_(a, a));
	}
	let temp_77_0 = (mul_((mul_(b, a)), (mul_(c, c))));
	let temp_77_1 = (mul_((mul_(b, a)), (mul_(c, c))));
	assert(eq_(temp_77_0, temp_77_1)) by {
		lemma_eq_ref(temp_77_0);
	}
	let temp_78_0 = (mod_((mul_((add_(c, b)), (mul_(c, a)))), m));
	let temp_78_1 = (mod_((mul_((add_(b, c)), (mul_(c, a)))), m));
	assert(eq_(temp_78_0, temp_78_1)) by {
		lemma_add_comm(c, b);
		cong_mod_(mul_(add_(c, b), mul_(c, a)), m, mul_(add_(b, c), mul_(c, a)), m);
		lemma_eq_ref(mul_(c, a));
		cong_mul_(add_(c, b), mul_(c, a), add_(b, c), mul_(c, a));
		lemma_eq_ref(m);
	}
	let temp_79_0 = (mul_((mul_(b, a)), (mul_(a, c))));
	let temp_79_1 = (mul_((mul_((mul_(b, a)), a)), c));
	assert(eq_(temp_79_0, temp_79_1)) by {
		lemma_mul_assoc(mul_(b, a), a, c);
	}
	let temp_80_0 = (mul_((mul_(a, c)), (mul_(a, b))));
	let temp_80_1 = (mul_((mul_(a, b)), (mul_(a, c))));
	assert(eq_(temp_80_0, temp_80_1)) by {
		lemma_mul_comm(mul_(a, c), mul_(a, b));
	}
	let temp_81_0 = (mul_((mul_(a, a)), (sub_(b, d))));
	let temp_81_1 = (mul_((mul_(a, a)), (sub_(b, d))));
	assert(eq_(temp_81_0, temp_81_1)) by {
		lemma_eq_ref(temp_81_0);
	}
	let temp_82_0 = (mod_((mul_((mul_(c, d)), (mod_((add_(c, a)), m)))), m));
	let temp_82_1 = (mod_((mod_((mul_((mul_(c, d)), (add_(c, a)))), m)), m));
	assert(eq_(temp_82_0, temp_82_1)) by {
		lemma_mod_mul_noop(mul_(c, d), add_(c, a), m);
		lemma_eq_sym(temp_82_1, temp_82_0);
	}
	let temp_83_0 = (mul_((mul_(b, d)), (mul_(d, d))));
	let temp_83_1 = (mul_(b, (mul_(d, (mul_(d, d))))));
	assert(eq_(temp_83_0, temp_83_1)) by {
		lemma_eq_sym(temp_83_1, temp_83_0);
		lemma_mul_assoc(b, d, mul_(d, d));
	}
	let temp_84_0 = (mul_((mul_(c, c)), (mul_(d, (mod_(b, m))))));
	let temp_84_1 = (mul_((mul_(c, c)), (mul_(d, (mod_(b, m))))));
	assert(eq_(temp_84_0, temp_84_1)) by {
		lemma_eq_ref(temp_84_0);
	}
	let temp_85_0 = (mul_((mul_(b, b)), (add_(d, (mod_(b, m))))));
	let temp_85_1 = (add_((mul_((mul_(b, b)), d)), (mul_((mul_(b, b)), (mod_(b, m))))));
	assert(eq_(temp_85_0, temp_85_1)) by {
		lemma_mul_dist(mul_(b, b), d, mod_(b, m));
	}
	let temp_86_0 = (mul_((add_(a, d)), (mul_(a, a))));
	let temp_86_1 = (mul_((mul_(a, a)), (add_(a, d))));
	assert(eq_(temp_86_0, temp_86_1)) by {
		lemma_mul_comm(add_(a, d), mul_(a, a));
	}
	let temp_87_0 = (mul_((mod_((sub_(d, b)), m)), (mul_(d, a))));
	let temp_87_1 = (mul_((mul_(d, a)), (mod_((sub_(d, b)), m))));
	assert(eq_(temp_87_0, temp_87_1)) by {
		lemma_mul_comm(mod_(sub_(d, b), m), mul_(d, a));
	}
	let temp_88_0 = (mul_((mul_(d, a)), (mul_(a, b))));
	let temp_88_1 = (mul_((mul_(a, d)), (mul_(a, b))));
	assert(eq_(temp_88_0, temp_88_1)) by {
		cong_mul_(mul_(d, a), mul_(a, b), mul_(a, d), mul_(a, b));
		lemma_mul_comm(d, a);
		lemma_eq_ref(mul_(a, b));
	}
	let temp_89_0 = (mul_((mul_(d, a)), (mul_(b, (mod_(d, m))))));
	let temp_89_1 = (mul_((mul_(d, a)), (mul_(b, (mod_((add_(d, (mul_((mod_((mul_((mul_(c, (mod_(b, m)))), (mul_(d, d)))), m)), m)))), m))))));
	assert(eq_(temp_89_0, temp_89_1)) by {
		lemma_mod_mul_vanish(d, mod_(mul_(mul_(c, mod_(b, m)), mul_(d, d)), m), m);
		cong_mul_(mul_(d, a), mul_(b, mod_(d, m)), mul_(d, a), mul_(b, mod_(add_(d, mul_(mod_(mul_(mul_(c, mod_(b, m)), mul_(d, d)), m), m)), m)));
		lemma_eq_ref(b);
		lemma_eq_ref(mul_(d, a));
		cong_mul_(b, mod_(d, m), b, mod_(add_(d, mul_(mod_(mul_(mul_(c, mod_(b, m)), mul_(d, d)), m), m)), m));
	}
	let temp_90_0 = (mul_((mul_(c, d)), (mul_(a, a))));
	let temp_90_1 = (mul_((mul_((mul_(c, d)), a)), a));
	assert(eq_(temp_90_0, temp_90_1)) by {
		lemma_mul_assoc(mul_(c, d), a, a);
	}
	let temp_91_0 = (mul_(b, (sub_(as_elem(74), a))));
	let temp_91_1 = (mul_((sub_(as_elem(74), a)), b));
	assert(eq_(temp_91_0, temp_91_1)) by {
		lemma_mul_comm(b, sub_(as_elem(74), a));
	}
	let temp_92_0 = (mul_((mul_(c, b)), (mul_(c, b))));
	let temp_92_1 = (mul_((mul_((mul_(c, b)), c)), b));
	assert(eq_(temp_92_0, temp_92_1)) by {
		lemma_mul_assoc(mul_(c, b), c, b);
	}
	let temp_93_0 = (mul_((add_(as_elem(52), a)), (add_(a, (mod_(d, m))))));
	let temp_93_1 = (mul_((add_(as_elem(52), a)), (add_((mod_(d, m)), a))));
	assert(eq_(temp_93_0, temp_93_1)) by {
		lemma_add_comm(a, mod_(d, m));
		cong_mul_(add_(as_elem(52), a), add_(a, mod_(d, m)), add_(as_elem(52), a), add_(mod_(d, m), a));
		lemma_eq_ref(add_(as_elem(52), a));
	}
	let temp_94_0 = (mul_((mul_(c, b)), (sub_(c, c))));
	let temp_94_1 = (mul_((sub_(c, c)), (mul_(c, b))));
	assert(eq_(temp_94_0, temp_94_1)) by {
		lemma_mul_comm(mul_(c, b), sub_(c, c));
	}
	let temp_95_0 = (mul_((sub_(b, d)), (mul_(b, d))));
	let temp_95_1 = (mul_((mul_(b, d)), (sub_(b, d))));
	assert(eq_(temp_95_0, temp_95_1)) by {
		lemma_mul_comm(sub_(b, d), mul_(b, d));
	}
	let temp_96_0 = (mul_((mul_(b, c)), (mul_(b, d))));
	let temp_96_1 = (mul_((mul_(c, b)), (mul_(b, d))));
	assert(eq_(temp_96_0, temp_96_1)) by {
		cong_mul_(mul_(b, c), mul_(b, d), mul_(c, b), mul_(b, d));
		lemma_mul_comm(b, c);
		lemma_eq_ref(mul_(b, d));
	}
	let temp_97_0 = (mul_((mul_(d, (mod_(d, m)))), (mul_(d, c))));
	let temp_97_1 = (mul_((mul_((mod_(d, m)), d)), (mul_(d, c))));
	assert(eq_(temp_97_0, temp_97_1)) by {
		cong_mul_(mul_(d, mod_(d, m)), mul_(d, c), mul_(mod_(d, m), d), mul_(d, c));
		lemma_mul_comm(d, mod_(d, m));
		lemma_eq_ref(mul_(d, c));
	}
	let temp_98_0 = (mul_((mul_(c, a)), (mul_(b, b))));
	let temp_98_1 = (mul_((mul_((mul_(c, a)), b)), b));
	assert(eq_(temp_98_0, temp_98_1)) by {
		lemma_mul_assoc(mul_(c, a), b, b);
	}
	let temp_99_0 = (mul_((mod_((mul_(c, b)), m)), (mul_(a, a))));
	let temp_99_1 = (mul_((mul_((mod_((mul_(c, b)), m)), a)), a));
	assert(eq_(temp_99_0, temp_99_1)) by {
		lemma_mul_assoc(mod_(mul_(c, b), m), a, a);
	}
	let temp_100_0 = (mul_((sub_(c, c)), (mul_((mod_(d, m)), (mod_(b, m))))));
	let temp_100_1 = (mul_((mul_((sub_(c, c)), (mod_(d, m)))), (mod_(b, m))));
	assert(eq_(temp_100_0, temp_100_1)) by {
		lemma_mul_assoc(sub_(c, c), mod_(d, m), mod_(b, m));
	}
	let temp_101_0 = (mul_((mul_(c, (mod_(a, m)))), c));
	let temp_101_1 = (mul_((mul_((mod_(a, m)), c)), c));
	assert(eq_(temp_101_0, temp_101_1)) by {
		cong_mul_(mul_(c, mod_(a, m)), c, mul_(mod_(a, m), c), c);
		lemma_mul_comm(c, mod_(a, m));
		lemma_eq_ref(c);
	}
	let temp_102_0 = (mul_((mul_(b, d)), (mul_(a, d))));
	let temp_102_1 = (mul_((mul_(b, d)), (mul_(d, a))));
	assert(eq_(temp_102_0, temp_102_1)) by {
		cong_mul_(mul_(b, d), mul_(a, d), mul_(b, d), mul_(d, a));
		lemma_mul_comm(a, d);
		lemma_eq_ref(mul_(b, d));
	}
	let temp_103_0 = (mul_((mod_((sub_(d, a)), m)), (mul_(b, d))));
	let temp_103_1 = (mul_((mod_((sub_(d, a)), m)), (mul_(d, b))));
	assert(eq_(temp_103_0, temp_103_1)) by {
		lemma_mul_comm(b, d);
		cong_mul_(mod_(sub_(d, a), m), mul_(b, d), mod_(sub_(d, a), m), mul_(d, b));
		lemma_eq_ref(mod_(sub_(d, a), m));
	}
	let temp_104_0 = (mul_((mul_((mod_(c, m)), d)), c));
	let temp_104_1 = (mul_((mul_((mod_((add_(c, (mul_((mul_((mul_((mod_(c, m)), b)), (mul_((mod_(as_elem(63), m)), c)))), m)))), m)), d)), c));
	assert(eq_(temp_104_0, temp_104_1)) by {
		lemma_eq_ref(d);
		lemma_mod_mul_vanish(c, mul_(mul_(mod_(c, m), b), mul_(mod_(as_elem(63), m), c)), m);
		cong_mul_(mul_(mod_(c, m), d), c, mul_(mod_(add_(c, mul_(mul_(mul_(mod_(c, m), b), mul_(mod_(as_elem(63), m), c)), m)), m), d), c);
		cong_mul_(mod_(c, m), d, mod_(add_(c, mul_(mul_(mul_(mod_(c, m), b), mul_(mod_(as_elem(63), m), c)), m)), m), d);
		lemma_eq_ref(c);
	}
	let temp_105_0 = (mul_((mul_(a, a)), (sub_(c, d))));
	let temp_105_1 = (mul_((sub_(c, d)), (mul_(a, a))));
	assert(eq_(temp_105_0, temp_105_1)) by {
		lemma_mul_comm(mul_(a, a), sub_(c, d));
	}
	let temp_106_0 = (mul_((mul_(a, (mod_(a, m)))), (mul_(d, b))));
	let temp_106_1 = (mul_((mul_((mul_(a, (mod_(a, m)))), d)), b));
	assert(eq_(temp_106_0, temp_106_1)) by {
		lemma_mul_assoc(mul_(a, mod_(a, m)), d, b);
	}
	let temp_107_0 = (mod_((mul_((add_(d, (mod_(c, m)))), (mul_(c, a)))), m));
	let temp_107_1 = (mod_((mul_((mul_((add_(d, (mod_(c, m)))), c)), a)), m));
	assert(eq_(temp_107_0, temp_107_1)) by {
		lemma_mul_assoc(add_(d, mod_(c, m)), c, a);
		cong_mod_(mul_(add_(d, mod_(c, m)), mul_(c, a)), m, mul_(mul_(add_(d, mod_(c, m)), c), a), m);
		lemma_eq_ref(m);
	}
	let temp_108_0 = (mul_((sub_(c, c)), (mul_((mod_(a, m)), as_elem(95)))));
	let temp_108_1 = (mul_((mul_((mod_(a, m)), as_elem(95))), (sub_(c, c))));
	assert(eq_(temp_108_0, temp_108_1)) by {
		lemma_mul_comm(sub_(c, c), mul_(mod_(a, m), as_elem(95)));
	}
	let temp_109_0 = (mul_((mul_((mod_(b, m)), (mod_(d, m)))), (mul_(d, b))));
	let temp_109_1 = (mul_((mul_(d, b)), (mul_((mod_(b, m)), (mod_(d, m))))));
	assert(eq_(temp_109_0, temp_109_1)) by {
		lemma_mul_comm(mul_(mod_(b, m), mod_(d, m)), mul_(d, b));
	}
	let temp_110_0 = (mul_((mod_((add_(a, c)), m)), (mul_(b, b))));
	let temp_110_1 = (mul_((mul_((mod_((add_(a, c)), m)), b)), b));
	assert(eq_(temp_110_0, temp_110_1)) by {
		lemma_mul_assoc(mod_(add_(a, c), m), b, b);
	}
	let temp_111_0 = (mul_((add_(a, b)), (add_(a, d))));
	let temp_111_1 = (add_((mul_((add_(a, b)), a)), (mul_((add_(a, b)), d))));
	assert(eq_(temp_111_0, temp_111_1)) by {
		lemma_mul_dist(add_(a, b), a, d);
	}
	let temp_112_0 = (mul_((mul_(b, b)), (mul_(as_elem(53), (mod_(d, m))))));
	let temp_112_1 = (mul_((mul_(b, b)), (mul_((mod_(d, m)), as_elem(53)))));
	assert(eq_(temp_112_0, temp_112_1)) by {
		lemma_mul_comm(as_elem(53), mod_(d, m));
		cong_mul_(mul_(b, b), mul_(as_elem(53), mod_(d, m)), mul_(b, b), mul_(mod_(d, m), as_elem(53)));
		lemma_eq_ref(mul_(b, b));
	}
	let temp_113_0 = (mul_((mul_(b, d)), (mul_((mod_(b, m)), d))));
	let temp_113_1 = (mul_((mul_(d, b)), (mul_((mod_(b, m)), d))));
	assert(eq_(temp_113_0, temp_113_1)) by {
		cong_mul_(mul_(b, d), mul_(mod_(b, m), d), mul_(d, b), mul_(mod_(b, m), d));
		lemma_mul_comm(b, d);
		lemma_eq_ref(mul_(mod_(b, m), d));
	}
	let temp_114_0 = (add_((mul_(c, c)), (mul_(c, b))));
	let temp_114_1 = (add_((mul_(c, b)), (mul_(c, c))));
	assert(eq_(temp_114_0, temp_114_1)) by {
		lemma_add_comm(mul_(c, c), mul_(c, b));
	}
	let temp_115_0 = (mul_(a, (mul_(b, a))));
	let temp_115_1 = (mul_((mul_(a, b)), a));
	assert(eq_(temp_115_0, temp_115_1)) by {
		lemma_mul_assoc(a, b, a);
	}
	let temp_116_0 = (mul_((mul_(a, b)), (add_(b, d))));
	let temp_116_1 = (mul_((mul_(a, b)), (add_(d, b))));
	assert(eq_(temp_116_0, temp_116_1)) by {
		cong_mul_(mul_(a, b), add_(b, d), mul_(a, b), add_(d, b));
		lemma_add_comm(b, d);
		lemma_eq_ref(mul_(a, b));
	}
	let temp_117_0 = (mul_((mul_(b, (mod_(b, m)))), (mul_(a, a))));
	let temp_117_1 = (mul_(b, (mul_((mod_(b, m)), (mul_(a, a))))));
	assert(eq_(temp_117_0, temp_117_1)) by {
		lemma_eq_sym(temp_117_1, temp_117_0);
		lemma_mul_assoc(b, mod_(b, m), mul_(a, a));
	}
	let temp_118_0 = (add_((sub_(d, b)), (mul_(c, c))));
	let temp_118_1 = (add_((sub_(d, b)), (mul_(c, c))));
	assert(eq_(temp_118_0, temp_118_1)) by {
		lemma_eq_ref(temp_118_0);
	}
	let temp_119_0 = (mul_((mul_(a, (mod_(c, m)))), (mul_(d, a))));
	let temp_119_1 = (mul_((mul_((mod_(c, m)), a)), (mul_(d, a))));
	assert(eq_(temp_119_0, temp_119_1)) by {
		lemma_mul_comm(a, mod_(c, m));
		cong_mul_(mul_(a, mod_(c, m)), mul_(d, a), mul_(mod_(c, m), a), mul_(d, a));
		lemma_eq_ref(mul_(d, a));
	}
	let temp_120_0 = (add_((mod_((mul_(c, c)), m)), (mul_(d, a))));
	let temp_120_1 = (add_((mul_(d, a)), (mod_((mul_(c, c)), m))));
	assert(eq_(temp_120_0, temp_120_1)) by {
		lemma_add_comm(mod_(mul_(c, c), m), mul_(d, a));
	}
	let temp_121_0 = (mul_((mod_((mul_(d, b)), m)), (mul_(b, d))));
	let temp_121_1 = (mul_((mod_((mul_(d, b)), m)), (mul_(d, b))));
	assert(eq_(temp_121_0, temp_121_1)) by {
		cong_mul_(mod_(mul_(d, b), m), mul_(b, d), mod_(mul_(d, b), m), mul_(d, b));
		lemma_mul_comm(b, d);
		lemma_eq_ref(mod_(mul_(d, b), m));
	}
	let temp_122_0 = (mul_((mul_(b, b)), (mul_(as_elem(80), (mod_(d, m))))));
	let temp_122_1 = (mul_((mul_(b, b)), (mul_((mod_(d, m)), as_elem(80)))));
	assert(eq_(temp_122_0, temp_122_1)) by {
		lemma_mul_comm(as_elem(80), mod_(d, m));
		cong_mul_(mul_(b, b), mul_(as_elem(80), mod_(d, m)), mul_(b, b), mul_(mod_(d, m), as_elem(80)));
		lemma_eq_ref(mul_(b, b));
	}
	let temp_123_0 = (mul_((mul_(d, (mod_(d, m)))), (sub_(b, c))));
	let temp_123_1 = (mul_(d, (mul_((mod_(d, m)), (sub_(b, c))))));
	assert(eq_(temp_123_0, temp_123_1)) by {
		lemma_mul_assoc(d, mod_(d, m), sub_(b, c));
		lemma_eq_sym(temp_123_1, temp_123_0);
	}
	let temp_124_0 = (mul_((mul_(a, d)), (mod_((mul_(a, b)), m))));
	let temp_124_1 = (mul_(a, (mul_(d, (mod_((mul_(a, b)), m))))));
	assert(eq_(temp_124_0, temp_124_1)) by {
		lemma_mul_assoc(a, d, mod_(mul_(a, b), m));
		lemma_eq_sym(temp_124_1, temp_124_0);
	}
	let temp_125_0 = (mul_((mul_(a, a)), (mul_(a, a))));
	let temp_125_1 = (mul_((mul_(a, a)), (mul_(a, a))));
	assert(eq_(temp_125_0, temp_125_1)) by {
		lemma_eq_ref(temp_125_0);
	}
	let temp_126_0 = (mul_((mul_(b, a)), (mul_((mod_(b, m)), a))));
	let temp_126_1 = (mul_((mul_((mul_(b, a)), (mod_(b, m)))), a));
	assert(eq_(temp_126_0, temp_126_1)) by {
		lemma_mul_assoc(mul_(b, a), mod_(b, m), a);
	}
	let temp_127_0 = (mul_((mul_(b, c)), (mul_(c, (mod_(c, m))))));
	let temp_127_1 = (mul_((mul_(b, c)), (mul_((mod_(c, m)), c))));
	assert(eq_(temp_127_0, temp_127_1)) by {
		cong_mul_(mul_(b, c), mul_(c, mod_(c, m)), mul_(b, c), mul_(mod_(c, m), c));
		lemma_mul_comm(c, mod_(c, m));
		lemma_eq_ref(mul_(b, c));
	}
	let temp_128_0 = (mul_((mul_(d, b)), (sub_(b, as_elem(23)))));
	let temp_128_1 = (mul_((sub_(b, as_elem(23))), (mul_(d, b))));
	assert(eq_(temp_128_0, temp_128_1)) by {
		lemma_mul_comm(mul_(d, b), sub_(b, as_elem(23)));
	}
	let temp_129_0 = (add_((mod_((mul_(b, as_elem(100))), m)), (mul_(c, as_elem(51)))));
	let temp_129_1 = (add_((mod_((mul_(as_elem(100), b)), m)), (mul_(c, as_elem(51)))));
	assert(eq_(temp_129_0, temp_129_1)) by {
		lemma_mul_comm(b, as_elem(100));
		cong_add_(mod_(mul_(b, as_elem(100)), m), mul_(c, as_elem(51)), mod_(mul_(as_elem(100), b), m), mul_(c, as_elem(51)));
		lemma_eq_ref(m);
		cong_mod_(mul_(b, as_elem(100)), m, mul_(as_elem(100), b), m);
		lemma_eq_ref(mul_(c, as_elem(51)));
	}
	let temp_130_0 = (mul_((mul_(a, d)), (mul_(b, c))));
	let temp_130_1 = (mul_((mul_(a, d)), (mul_(c, b))));
	assert(eq_(temp_130_0, temp_130_1)) by {
		cong_mul_(mul_(a, d), mul_(b, c), mul_(a, d), mul_(c, b));
		lemma_mul_comm(b, c);
		lemma_eq_ref(mul_(a, d));
	}
	let temp_131_0 = (mul_((mul_(a, b)), (mul_(d, (mod_(d, m))))));
	let temp_131_1 = (mul_((mul_((mul_(a, b)), d)), (mod_(d, m))));
	assert(eq_(temp_131_0, temp_131_1)) by {
		lemma_mul_assoc(mul_(a, b), d, mod_(d, m));
	}
	let temp_132_0 = (mul_((mul_(a, d)), (mul_(d, b))));
	let temp_132_1 = (mul_(a, (mul_(d, (mul_(d, b))))));
	assert(eq_(temp_132_0, temp_132_1)) by {
		lemma_eq_sym(temp_132_1, temp_132_0);
		lemma_mul_assoc(a, d, mul_(d, b));
	}
	let temp_133_0 = (mod_((mul_((sub_(b, a)), (mod_((mul_(b, d)), m)))), m));
	let temp_133_1 = (mod_((mul_((sub_(b, a)), (mod_((add_((mul_((add_((mul_(c, (mod_(b, m)))), (mul_(c, (mod_(c, m)))))), m)), (mul_(b, d)))), m)))), m));
	assert(eq_(temp_133_0, temp_133_1)) by {
		lemma_mod_mul_vanish(mul_(b, d), add_(mul_(c, mod_(b, m)), mul_(c, mod_(c, m))), m);
		cong_mod_(mul_(sub_(b, a), mod_(mul_(b, d), m)), m, mul_(sub_(b, a), mod_(add_(mul_(add_(mul_(c, mod_(b, m)), mul_(c, mod_(c, m))), m), mul_(b, d)), m)), m);
		lemma_eq_ref(m);
		lemma_eq_ref(sub_(b, a));
		cong_mul_(sub_(b, a), mod_(mul_(b, d), m), sub_(b, a), mod_(add_(mul_(add_(mul_(c, mod_(b, m)), mul_(c, mod_(c, m))), m), mul_(b, d)), m));
	}
	let temp_134_0 = (add_((mul_(a, a)), (mul_(a, c))));
	let temp_134_1 = (add_((mul_(a, c)), (mul_(a, a))));
	assert(eq_(temp_134_0, temp_134_1)) by {
		lemma_add_comm(mul_(a, a), mul_(a, c));
	}
	let temp_135_0 = (mul_((mul_(d, a)), (mul_(d, d))));
	let temp_135_1 = (mul_(d, (mul_(a, (mul_(d, d))))));
	assert(eq_(temp_135_0, temp_135_1)) by {
		lemma_eq_sym(temp_135_1, temp_135_0);
		lemma_mul_assoc(d, a, mul_(d, d));
	}
	let temp_136_0 = (mul_((mul_(a, a)), (sub_((mod_(d, m)), b))));
	let temp_136_1 = (mul_((mul_(a, a)), (sub_((mod_(d, m)), b))));
	assert(eq_(temp_136_0, temp_136_1)) by {
		lemma_eq_ref(temp_136_0);
	}
	let temp_137_0 = (mul_((mul_(b, (mod_(c, m)))), (mod_((sub_(a, as_elem(75))), m))));
	let temp_137_1 = (mul_((mul_(b, (mod_((add_((mul_((mul_((mul_(c, b)), (mul_(c, d)))), m)), c)), m)))), (mod_((sub_(a, as_elem(75))), m))));
	assert(eq_(temp_137_0, temp_137_1)) by {
		lemma_mod_mul_vanish(c, mul_(mul_(c, b), mul_(c, d)), m);
		cong_mul_(mul_(b, mod_(c, m)), mod_(sub_(a, as_elem(75)), m), mul_(b, mod_(add_(mul_(mul_(mul_(c, b), mul_(c, d)), m), c), m)), mod_(sub_(a, as_elem(75)), m));
		lemma_eq_ref(b);
		cong_mul_(b, mod_(c, m), b, mod_(add_(mul_(mul_(mul_(c, b), mul_(c, d)), m), c), m));
		lemma_eq_ref(mod_(sub_(a, as_elem(75)), m));
	}
	let temp_138_0 = (mod_((mul_((mul_(d, d)), (mul_(d, b)))), m));
	let temp_138_1 = (mod_((add_((mul_((mul_(d, d)), (mul_(d, b)))), (mul_((mul_((mul_(d, a)), (mul_(c, b)))), m)))), m));
	assert(eq_(temp_138_0, temp_138_1)) by {
		lemma_mod_mul_vanish(mul_(mul_(d, d), mul_(d, b)), mul_(mul_(d, a), mul_(c, b)), m);
	}
	let temp_139_0 = (mul_((mul_(d, c)), (mul_(c, d))));
	let temp_139_1 = (mul_((mul_((mul_(d, c)), c)), d));
	assert(eq_(temp_139_0, temp_139_1)) by {
		lemma_mul_assoc(mul_(d, c), c, d);
	}
	let temp_140_0 = (mul_(a, (mod_((mul_(a, b)), m))));
	let temp_140_1 = (mul_((mod_((mul_(a, b)), m)), a));
	assert(eq_(temp_140_0, temp_140_1)) by {
		lemma_mul_comm(a, mod_(mul_(a, b), m));
	}
	let temp_141_0 = (mul_((mul_(d, a)), (add_(b, a))));
	let temp_141_1 = (mul_((mul_(d, a)), (add_(a, b))));
	assert(eq_(temp_141_0, temp_141_1)) by {
		cong_mul_(mul_(d, a), add_(b, a), mul_(d, a), add_(a, b));
		lemma_add_comm(b, a);
		lemma_eq_ref(mul_(d, a));
	}
	let temp_142_0 = (add_((sub_(a, a)), (mul_(d, c))));
	let temp_142_1 = (add_((mul_(d, c)), (sub_(a, a))));
	assert(eq_(temp_142_0, temp_142_1)) by {
		lemma_add_comm(sub_(a, a), mul_(d, c));
	}
	let temp_143_0 = (mul_((mul_(b, b)), (mul_(d, c))));
	let temp_143_1 = (mul_((mul_(b, b)), (mul_(d, c))));
	assert(eq_(temp_143_0, temp_143_1)) by {
		lemma_eq_ref(temp_143_0);
	}
	let temp_144_0 = (mod_((sub_((add_(c, a)), (mul_((mod_(b, m)), c)))), m));
	let temp_144_1 = (mod_((sub_((add_(a, c)), (mul_((mod_(b, m)), c)))), m));
	assert(eq_(temp_144_0, temp_144_1)) by {
		lemma_add_comm(c, a);
		cong_mod_(sub_(add_(c, a), mul_(mod_(b, m), c)), m, sub_(add_(a, c), mul_(mod_(b, m), c)), m);
		lemma_eq_ref(mul_(mod_(b, m), c));
		lemma_eq_ref(m);
		cong_sub_(add_(c, a), mul_(mod_(b, m), c), add_(a, c), mul_(mod_(b, m), c));
	}
	let temp_145_0 = (mul_((mul_((mod_(a, m)), a)), (add_(d, b))));
	let temp_145_1 = (add_((mul_((mul_((mod_(a, m)), a)), d)), (mul_((mul_((mod_(a, m)), a)), b))));
	assert(eq_(temp_145_0, temp_145_1)) by {
		lemma_mul_dist(mul_(mod_(a, m), a), d, b);
	}
	let temp_146_0 = (mul_((sub_(c, c)), (mul_(d, (mod_(c, m))))));
	let temp_146_1 = (sub_((mul_(c, (mul_(d, (mod_(c, m)))))), (mul_(c, (mul_(d, (mod_(c, m))))))));
	assert(eq_(temp_146_0, temp_146_1)) by {
		lemma_mul_dist(mul_(d, mod_(c, m)), c, c);
	}
	let temp_147_0 = (mul_((mul_(d, c)), (mul_(c, c))));
	let temp_147_1 = (mul_((mul_(d, c)), (mul_(c, c))));
	assert(eq_(temp_147_0, temp_147_1)) by {
		lemma_eq_ref(temp_147_0);
	}

}

} // verus!