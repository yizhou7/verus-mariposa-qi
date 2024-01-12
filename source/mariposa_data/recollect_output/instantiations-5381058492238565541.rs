use builtin_macros::*;
// use builtin::*;
mod nl_basics;
use crate::nl_basics::*;
verus! {

pub proof fn free_0(a: Elem, b: Elem, c: Elem, d: Elem, m: Elem)
{
	let temp_0_0 = (mul_((mul_(d, a)), (mul_(a, a))));
	let temp_0_1 = (mul_((mul_(a, a)), (mul_(d, a))));
	assert(eq_(temp_0_0, temp_0_1)) by {
		lemma_mul_comm(mul_(d, a), mul_(a, a));
	}
	let temp_1_0 = (sub_((mul_((mod_(a, m)), (mod_(d, m)))), (mul_(b, c))));
	let temp_1_1 = (sub_((mul_((mod_((add_(a, (mul_((mul_((mul_(c, d)), (add_(b, b)))), m)))), m)), (mod_(d, m)))), (mul_(b, c))));
	assert(eq_(temp_1_0, temp_1_1)) by {
		lemma_mod_mul_vanish(a, mul_(mul_(c, d), add_(b, b)), m);
		cong_sub_(mul_(mod_(a, m), mod_(d, m)), mul_(b, c), mul_(mod_(add_(a, mul_(mul_(mul_(c, d), add_(b, b)), m)), m), mod_(d, m)), mul_(b, c));
		lemma_eq_ref(mod_(d, m));
		cong_mul_(mod_(a, m), mod_(d, m), mod_(add_(a, mul_(mul_(mul_(c, d), add_(b, b)), m)), m), mod_(d, m));
		lemma_eq_ref(mul_(b, c));
	}
	let temp_2_0 = (mod_((mul_((mod_((mul_(a, b)), m)), (mul_(b, c)))), m));
	let temp_2_1 = (mod_((mul_((mod_((mul_(b, a)), m)), (mul_(b, c)))), m));
	assert(eq_(temp_2_0, temp_2_1)) by {
		lemma_mul_comm(a, b);
		cong_mod_(mul_(mod_(mul_(a, b), m), mul_(b, c)), m, mul_(mod_(mul_(b, a), m), mul_(b, c)), m);
		cong_mul_(mod_(mul_(a, b), m), mul_(b, c), mod_(mul_(b, a), m), mul_(b, c));
		lemma_eq_ref(m);
		lemma_eq_ref(mul_(b, c));
		cong_mod_(mul_(a, b), m, mul_(b, a), m);
	}
	let temp_3_0 = (mul_((mul_(b, d)), (mul_((mod_(a, m)), b))));
	let temp_3_1 = (mul_((mul_(b, d)), (mul_(b, (mod_(a, m))))));
	assert(eq_(temp_3_0, temp_3_1)) by {
		lemma_mul_comm(mod_(a, m), b);
		cong_mul_(mul_(b, d), mul_(mod_(a, m), b), mul_(b, d), mul_(b, mod_(a, m)));
		lemma_eq_ref(mul_(b, d));
	}
	let temp_4_0 = (mul_((mul_(c, d)), (mod_((mul_(a, b)), m))));
	let temp_4_1 = (mul_(c, (mul_(d, (mod_((mul_(a, b)), m))))));
	assert(eq_(temp_4_0, temp_4_1)) by {
		lemma_mul_assoc(c, d, mod_(mul_(a, b), m));
		lemma_eq_sym(temp_4_1, temp_4_0);
	}
	let temp_5_0 = (mul_((mod_((mul_(b, b)), m)), (mod_((sub_(a, c)), m))));
	let temp_5_1 = (mul_((mod_((mul_(b, b)), m)), (mod_((sub_((mod_(a, m)), (mod_(c, m)))), m))));
	assert(eq_(temp_5_0, temp_5_1)) by {
		cong_mul_(mod_(mul_(b, b), m), mod_(sub_(a, c), m), mod_(mul_(b, b), m), mod_(sub_(mod_(a, m), mod_(c, m)), m));
		lemma_mod_sub_noop(a, c, m);
		lemma_eq_ref(mod_(mul_(b, b), m));
	}
	let temp_6_0 = (mul_((mul_(a, c)), (mul_(c, as_elem(54)))));
	let temp_6_1 = (mul_((mul_(a, c)), (mul_(as_elem(54), c))));
	assert(eq_(temp_6_0, temp_6_1)) by {
		cong_mul_(mul_(a, c), mul_(c, as_elem(54)), mul_(a, c), mul_(as_elem(54), c));
		lemma_mul_comm(c, as_elem(54));
		lemma_eq_ref(mul_(a, c));
	}
	let temp_7_0 = (mul_((mul_(b, d)), (mul_(c, c))));
	let temp_7_1 = (mul_((mul_(c, c)), (mul_(b, d))));
	assert(eq_(temp_7_0, temp_7_1)) by {
		lemma_mul_comm(mul_(b, d), mul_(c, c));
	}
	let temp_8_0 = (mul_((sub_(d, d)), (mul_(a, d))));
	let temp_8_1 = (mul_((sub_(d, d)), (mul_(d, a))));
	assert(eq_(temp_8_0, temp_8_1)) by {
		cong_mul_(sub_(d, d), mul_(a, d), sub_(d, d), mul_(d, a));
		lemma_mul_comm(a, d);
		cong_sub_(d, d, d, d);
		lemma_eq_ref(d);
	}
	let temp_9_0 = (mul_((mul_((mod_(a, m)), d)), (mod_((mul_(c, a)), m))));
	let temp_9_1 = (mul_((mod_(a, m)), (mul_(d, (mod_((mul_(c, a)), m))))));
	assert(eq_(temp_9_0, temp_9_1)) by {
		lemma_mul_assoc(mod_(a, m), d, mod_(mul_(c, a), m));
		lemma_eq_sym(temp_9_1, temp_9_0);
	}
	let temp_10_0 = (add_((mul_(b, c)), (add_(c, d))));
	let temp_10_1 = (add_((add_(c, d)), (mul_(b, c))));
	assert(eq_(temp_10_0, temp_10_1)) by {
		lemma_add_comm(mul_(b, c), add_(c, d));
	}
	let temp_11_0 = (mul_((mul_(b, c)), (mul_(d, a))));
	let temp_11_1 = (mul_((mul_((mul_(b, c)), d)), a));
	assert(eq_(temp_11_0, temp_11_1)) by {
		lemma_mul_assoc(mul_(b, c), d, a);
	}
	let temp_12_0 = (mul_((mul_(d, b)), (add_(b, (mod_(a, m))))));
	let temp_12_1 = (mul_(d, (mul_(b, (add_(b, (mod_(a, m))))))));
	assert(eq_(temp_12_0, temp_12_1)) by {
		lemma_mul_assoc(d, b, add_(b, mod_(a, m)));
		lemma_eq_sym(temp_12_1, temp_12_0);
	}
	let temp_13_0 = (mul_((mul_(c, b)), (mul_((mod_(d, m)), (mod_(d, m))))));
	let temp_13_1 = (mul_((mul_((mul_(c, b)), (mod_(d, m)))), (mod_(d, m))));
	assert(eq_(temp_13_0, temp_13_1)) by {
		lemma_mul_assoc(mul_(c, b), mod_(d, m), mod_(d, m));
	}
	let temp_14_0 = (mod_((add_((mul_(b, c)), (mod_((sub_(b, d)), m)))), m));
	let temp_14_1 = (mod_((add_((mod_((sub_(b, d)), m)), (mul_(b, c)))), m));
	assert(eq_(temp_14_0, temp_14_1)) by {
		lemma_add_comm(mul_(b, c), mod_(sub_(b, d), m));
		cong_mod_(add_(mul_(b, c), mod_(sub_(b, d), m)), m, add_(mod_(sub_(b, d), m), mul_(b, c)), m);
		lemma_eq_ref(m);
	}
	let temp_15_0 = (mul_((mul_(a, b)), (mul_(a, (mod_(c, m))))));
	let temp_15_1 = (mul_((mul_(a, (mod_(c, m)))), (mul_(a, b))));
	assert(eq_(temp_15_0, temp_15_1)) by {
		lemma_mul_comm(mul_(a, b), mul_(a, mod_(c, m)));
	}
	let temp_16_0 = (sub_((mod_((mul_(b, c)), m)), (sub_(d, d))));
	let temp_16_1 = (sub_((mod_((mul_(c, b)), m)), (sub_(d, d))));
	assert(eq_(temp_16_0, temp_16_1)) by {
		lemma_mul_comm(b, c);
		cong_sub_(mod_(mul_(b, c), m), sub_(d, d), mod_(mul_(c, b), m), sub_(d, d));
		cong_mod_(mul_(b, c), m, mul_(c, b), m);
		lemma_eq_ref(sub_(d, d));
		lemma_eq_ref(m);
	}
	let temp_17_0 = (mul_((sub_(d, b)), (mul_(a, d))));
	let temp_17_1 = (sub_((mul_(d, (mul_(a, d)))), (mul_(b, (mul_(a, d))))));
	assert(eq_(temp_17_0, temp_17_1)) by {
		lemma_mul_dist(mul_(a, d), d, b);
	}
	let temp_18_0 = (mul_((mul_(a, a)), (mul_(c, a))));
	let temp_18_1 = (mul_(a, (mul_(a, (mul_(c, a))))));
	assert(eq_(temp_18_0, temp_18_1)) by {
		lemma_eq_sym(temp_18_1, temp_18_0);
		lemma_mul_assoc(a, a, mul_(c, a));
	}
	let temp_19_0 = (add_((mul_(d, d)), (mul_(a, d))));
	let temp_19_1 = (mul_((add_(d, a)), d));
	assert(eq_(temp_19_0, temp_19_1)) by {
		lemma_eq_sym(temp_19_1, temp_19_0);
		lemma_mul_dist(d, a, d);
	}
	let temp_20_0 = (mod_((sub_((mod_((mul_(a, b)), m)), (mul_(b, c)))), m));
	let temp_20_1 = (mod_((sub_((mod_((mod_((mul_(a, b)), m)), m)), (mul_(b, c)))), m));
	assert(eq_(temp_20_0, temp_20_1)) by {
		lemma_mod_sub_noop(mod_(mul_(a, b), m), mul_(b, c), m);
	}
	let temp_21_0 = (mod_((mul_((mul_(d, b)), (mul_(b, b)))), m));
	let temp_21_1 = (mod_((mul_((mul_((mul_(d, b)), b)), b)), m));
	assert(eq_(temp_21_0, temp_21_1)) by {
		lemma_mul_assoc(mul_(d, b), b, b);
		cong_mod_(mul_(mul_(d, b), mul_(b, b)), m, mul_(mul_(mul_(d, b), b), b), m);
		lemma_eq_ref(m);
	}
	let temp_22_0 = (mod_((mul_((add_((mod_(d, m)), c)), b)), m));
	let temp_22_1 = (mod_((add_((mul_((mod_(d, m)), b)), (mul_(c, b)))), m));
	assert(eq_(temp_22_0, temp_22_1)) by {
		lemma_mul_dist(mod_(d, m), c, b);
		cong_mod_(mul_(add_(mod_(d, m), c), b), m, add_(mul_(mod_(d, m), b), mul_(c, b)), m);
		lemma_eq_ref(m);
	}
	let temp_23_0 = (mul_((mul_((mod_(a, m)), a)), (mul_(b, (mod_(b, m))))));
	let temp_23_1 = (mul_((mul_((mod_(a, m)), a)), (mul_((mod_(b, m)), b))));
	assert(eq_(temp_23_0, temp_23_1)) by {
		lemma_mul_comm(b, mod_(b, m));
		cong_mul_(mul_(mod_(a, m), a), mul_(b, mod_(b, m)), mul_(mod_(a, m), a), mul_(mod_(b, m), b));
		lemma_eq_ref(mul_(mod_(a, m), a));
	}
	let temp_24_0 = (mul_((mul_((mod_(b, m)), c)), (mul_(a, d))));
	let temp_24_1 = (mul_((mul_(a, d)), (mul_((mod_(b, m)), c))));
	assert(eq_(temp_24_0, temp_24_1)) by {
		lemma_mul_comm(mul_(mod_(b, m), c), mul_(a, d));
	}
	let temp_25_0 = (mul_((mod_((mul_(c, c)), m)), (mod_((sub_(a, a)), m))));
	let temp_25_1 = (mul_((mod_((mul_(c, c)), m)), (mod_((sub_((mod_(a, m)), (mod_(a, m)))), m))));
	assert(eq_(temp_25_0, temp_25_1)) by {
		cong_mul_(mod_(mul_(c, c), m), mod_(sub_(a, a), m), mod_(mul_(c, c), m), mod_(sub_(mod_(a, m), mod_(a, m)), m));
		lemma_mod_sub_noop(a, a, m);
		lemma_eq_ref(mod_(mul_(c, c), m));
	}
	let temp_26_0 = (mod_((mul_((mul_(a, c)), (sub_((mod_(a, m)), c)))), m));
	let temp_26_1 = (mod_((mul_((sub_((mod_(a, m)), c)), (mul_(a, c)))), m));
	assert(eq_(temp_26_0, temp_26_1)) by {
		lemma_mul_comm(mul_(a, c), sub_(mod_(a, m), c));
		cong_mod_(mul_(mul_(a, c), sub_(mod_(a, m), c)), m, mul_(sub_(mod_(a, m), c), mul_(a, c)), m);
		lemma_eq_ref(m);
	}
	let temp_27_0 = (mul_((mul_(a, b)), (mul_(a, d))));
	let temp_27_1 = (mul_((mul_(a, b)), (mul_(d, a))));
	assert(eq_(temp_27_0, temp_27_1)) by {
		cong_mul_(mul_(a, b), mul_(a, d), mul_(a, b), mul_(d, a));
		lemma_mul_comm(a, d);
		lemma_eq_ref(mul_(a, b));
	}
	let temp_28_0 = (add_((sub_(c, a)), (mul_(c, a))));
	let temp_28_1 = (add_((mul_(c, a)), (sub_(c, a))));
	assert(eq_(temp_28_0, temp_28_1)) by {
		lemma_add_comm(sub_(c, a), mul_(c, a));
	}
	let temp_29_0 = (sub_((mul_(d, b)), (mul_(c, c))));
	let temp_29_1 = (sub_((mul_(b, d)), (mul_(c, c))));
	assert(eq_(temp_29_0, temp_29_1)) by {
		cong_sub_(mul_(d, b), mul_(c, c), mul_(b, d), mul_(c, c));
		lemma_mul_comm(d, b);
		lemma_mul_comm(c, c);
	}
	let temp_30_0 = (mul_((mul_(d, a)), (mul_(b, a))));
	let temp_30_1 = (mul_((mul_(b, a)), (mul_(d, a))));
	assert(eq_(temp_30_0, temp_30_1)) by {
		lemma_mul_comm(mul_(d, a), mul_(b, a));
	}
	let temp_31_0 = (mul_((mul_(b, a)), (mul_(a, b))));
	let temp_31_1 = (mul_((mul_((mul_(b, a)), a)), b));
	assert(eq_(temp_31_0, temp_31_1)) by {
		lemma_mul_assoc(mul_(b, a), a, b);
	}
	let temp_32_0 = (mod_((add_((mul_((mod_(c, m)), (mod_(d, m)))), (mul_(d, a)))), m));
	let temp_32_1 = (mod_((add_((mul_(d, a)), (mul_((mod_(c, m)), (mod_(d, m)))))), m));
	assert(eq_(temp_32_0, temp_32_1)) by {
		lemma_add_comm(mul_(mod_(c, m), mod_(d, m)), mul_(d, a));
		cong_mod_(add_(mul_(mod_(c, m), mod_(d, m)), mul_(d, a)), m, add_(mul_(d, a), mul_(mod_(c, m), mod_(d, m))), m);
		lemma_eq_ref(m);
	}
	let temp_33_0 = (mod_((sub_((mul_(d, (mod_(b, m)))), (mul_(c, b)))), m));
	let temp_33_1 = (mod_((sub_((sub_((mul_(d, (mod_(b, m)))), (mul_(c, b)))), (mul_((mul_((mul_(c, (mod_(b, m)))), (sub_(c, c)))), m)))), m));
	assert(eq_(temp_33_0, temp_33_1)) by {
		lemma_mod_mul_vanish(sub_(mul_(d, mod_(b, m)), mul_(c, b)), mul_(mul_(c, mod_(b, m)), sub_(c, c)), m);
	}
	let temp_34_0 = (mul_((mul_(c, as_elem(17))), (add_(c, d))));
	let temp_34_1 = (mul_(c, (mul_(as_elem(17), (add_(c, d))))));
	assert(eq_(temp_34_0, temp_34_1)) by {
		lemma_eq_sym(temp_34_1, temp_34_0);
		lemma_mul_assoc(c, as_elem(17), add_(c, d));
	}
	let temp_35_0 = (mul_((mul_(c, c)), (mul_(d, d))));
	let temp_35_1 = (mul_(c, (mul_(c, (mul_(d, d))))));
	assert(eq_(temp_35_0, temp_35_1)) by {
		lemma_eq_sym(temp_35_1, temp_35_0);
		lemma_mul_assoc(c, c, mul_(d, d));
	}
	let temp_36_0 = (mul_((mul_(b, d)), (sub_(a, a))));
	let temp_36_1 = (mul_((sub_(a, a)), (mul_(b, d))));
	assert(eq_(temp_36_0, temp_36_1)) by {
		lemma_mul_comm(mul_(b, d), sub_(a, a));
	}
	let temp_37_0 = (mul_((mul_(d, (mod_(d, m)))), (mul_(a, b))));
	let temp_37_1 = (mul_((mul_(a, b)), (mul_(d, (mod_(d, m))))));
	assert(eq_(temp_37_0, temp_37_1)) by {
		lemma_mul_comm(mul_(d, mod_(d, m)), mul_(a, b));
	}
	let temp_38_0 = (mul_((mul_((mod_(a, m)), c)), (mul_(d, c))));
	let temp_38_1 = (mul_((mul_((mul_((mod_(a, m)), c)), d)), c));
	assert(eq_(temp_38_0, temp_38_1)) by {
		lemma_mul_assoc(mul_(mod_(a, m), c), d, c);
	}
	let temp_39_0 = (add_((mul_(c, c)), (add_(d, d))));
	let temp_39_1 = (add_((add_(d, d)), (mul_(c, c))));
	assert(eq_(temp_39_0, temp_39_1)) by {
		lemma_add_comm(mul_(c, c), add_(d, d));
	}
	let temp_40_0 = (mul_((add_(a, c)), (mod_((mul_(b, a)), m))));
	let temp_40_1 = (mul_((add_(c, a)), (mod_((mul_(b, a)), m))));
	assert(eq_(temp_40_0, temp_40_1)) by {
		lemma_add_comm(a, c);
		cong_mul_(add_(a, c), mod_(mul_(b, a), m), add_(c, a), mod_(mul_(b, a), m));
		lemma_eq_ref(mod_(mul_(b, a), m));
	}
	let temp_41_0 = (mul_((mod_((mul_(b, c)), m)), (mul_(b, as_elem(27)))));
	let temp_41_1 = (mul_((mod_((sub_((mul_(b, c)), (mul_((mul_((mul_(c, b)), (mul_(d, as_elem(87))))), m)))), m)), (mul_(b, as_elem(27)))));
	assert(eq_(temp_41_0, temp_41_1)) by {
		cong_mul_(mod_(mul_(b, c), m), mul_(b, as_elem(27)), mod_(sub_(mul_(b, c), mul_(mul_(mul_(c, b), mul_(d, as_elem(87))), m)), m), mul_(b, as_elem(27)));
		lemma_mod_mul_vanish(mul_(b, c), mul_(mul_(c, b), mul_(d, as_elem(87))), m);
		lemma_eq_ref(mul_(b, as_elem(27)));
	}
	let temp_42_0 = (mod_((mul_((mul_(d, a)), (mul_(a, b)))), m));
	let temp_42_1 = (mod_((add_((mul_((mul_(d, a)), (mul_(a, b)))), (mul_((mul_((mul_(b, b)), (mod_((mul_(a, d)), m)))), m)))), m));
	assert(eq_(temp_42_0, temp_42_1)) by {
		lemma_mod_mul_vanish(mul_(mul_(d, a), mul_(a, b)), mul_(mul_(b, b), mod_(mul_(a, d), m)), m);
	}
	let temp_43_0 = (mod_((mul_((mul_((mod_(b, m)), d)), (mod_((mul_((mod_(a, m)), b)), m)))), m));
	let temp_43_1 = (mod_((mul_((mod_(b, m)), (mul_(d, (mod_((mul_((mod_(a, m)), b)), m)))))), m));
	assert(eq_(temp_43_0, temp_43_1)) by {
		lemma_mul_assoc(mod_(b, m), d, mod_(mul_(mod_(a, m), b), m));
		cong_mod_(mul_(mul_(mod_(b, m), d), mod_(mul_(mod_(a, m), b), m)), m, mul_(mod_(b, m), mul_(d, mod_(mul_(mod_(a, m), b), m))), m);
		lemma_eq_ref(m);
		lemma_eq_sym(mul_(mod_(b, m), mul_(d, mod_(mul_(mod_(a, m), b), m))), mul_(mul_(mod_(b, m), d), mod_(mul_(mod_(a, m), b), m)));
	}
	let temp_44_0 = (add_((mul_(d, d)), c));
	let temp_44_1 = (add_((mul_(d, d)), c));
	assert(eq_(temp_44_0, temp_44_1)) by {
		lemma_eq_ref(temp_44_0);
	}
	let temp_45_0 = (mod_((mul_((mul_(a, c)), (mul_((mod_(as_elem(18), m)), c)))), m));
	let temp_45_1 = (mod_((mul_((mul_(a, c)), (mul_(c, (mod_(as_elem(18), m)))))), m));
	assert(eq_(temp_45_0, temp_45_1)) by {
		lemma_mul_comm(mod_(as_elem(18), m), c);
		cong_mod_(mul_(mul_(a, c), mul_(mod_(as_elem(18), m), c)), m, mul_(mul_(a, c), mul_(c, mod_(as_elem(18), m))), m);
		lemma_eq_ref(m);
		lemma_eq_ref(mul_(a, c));
		cong_mul_(mul_(a, c), mul_(mod_(as_elem(18), m), c), mul_(a, c), mul_(c, mod_(as_elem(18), m)));
	}
	let temp_46_0 = (mul_((mod_((sub_(a, a)), m)), (mul_(a, b))));
	let temp_46_1 = (mul_((mod_((add_((sub_(a, a)), (mul_((mul_((mul_(d, b)), (mod_((mul_(c, b)), m)))), m)))), m)), (mul_(a, b))));
	assert(eq_(temp_46_0, temp_46_1)) by {
		lemma_mod_mul_vanish(sub_(a, a), mul_(mul_(d, b), mod_(mul_(c, b), m)), m);
		cong_mul_(mod_(sub_(a, a), m), mul_(a, b), mod_(add_(sub_(a, a), mul_(mul_(mul_(d, b), mod_(mul_(c, b), m)), m)), m), mul_(a, b));
		lemma_eq_ref(mul_(a, b));
	}
	let temp_47_0 = (mul_((mul_((mod_(as_elem(66), m)), d)), (mul_(d, a))));
	let temp_47_1 = (mul_((mul_((mul_((mod_(as_elem(66), m)), d)), d)), a));
	assert(eq_(temp_47_0, temp_47_1)) by {
		lemma_mul_assoc(mul_(mod_(as_elem(66), m), d), d, a);
	}
	let temp_48_0 = (mul_((mul_(a, a)), (mul_(b, c))));
	let temp_48_1 = (mul_((mul_(a, a)), (mul_(c, b))));
	assert(eq_(temp_48_0, temp_48_1)) by {
		cong_mul_(mul_(a, a), mul_(b, c), mul_(a, a), mul_(c, b));
		lemma_mul_comm(a, a);
		lemma_mul_comm(b, c);
	}
	let temp_49_0 = (mul_((mul_(b, d)), (mul_(d, a))));
	let temp_49_1 = (mul_((mul_((mul_(b, d)), d)), a));
	assert(eq_(temp_49_0, temp_49_1)) by {
		lemma_mul_assoc(mul_(b, d), d, a);
	}
	let temp_50_0 = (mul_((add_(d, a)), (mod_((mul_(b, d)), m))));
	let temp_50_1 = (mul_((add_(a, d)), (mod_((mul_(b, d)), m))));
	assert(eq_(temp_50_0, temp_50_1)) by {
		lemma_add_comm(d, a);
		cong_mul_(add_(d, a), mod_(mul_(b, d), m), add_(a, d), mod_(mul_(b, d), m));
		lemma_eq_ref(mod_(mul_(b, d), m));
	}
	let temp_51_0 = (mul_((mul_(d, a)), (sub_(b, (mod_(d, m))))));
	let temp_51_1 = (mul_(d, (mul_(a, (sub_(b, (mod_(d, m))))))));
	assert(eq_(temp_51_0, temp_51_1)) by {
		lemma_mul_assoc(d, a, sub_(b, mod_(d, m)));
		lemma_eq_sym(temp_51_1, temp_51_0);
	}
	let temp_52_0 = (mul_((mul_(d, b)), (mul_(b, d))));
	let temp_52_1 = (mul_((mul_(b, d)), (mul_(b, d))));
	assert(eq_(temp_52_0, temp_52_1)) by {
		cong_mul_(mul_(d, b), mul_(b, d), mul_(b, d), mul_(b, d));
		lemma_mul_comm(d, b);
		lemma_eq_ref(mul_(b, d));
	}
	let temp_53_0 = (mul_((mul_(c, c)), (mul_((mod_(a, m)), c))));
	let temp_53_1 = (mul_(c, (mul_(c, (mul_((mod_(a, m)), c))))));
	assert(eq_(temp_53_0, temp_53_1)) by {
		lemma_eq_sym(temp_53_1, temp_53_0);
		lemma_mul_assoc(c, c, mul_(mod_(a, m), c));
	}
	let temp_54_0 = (add_((sub_(c, a)), (add_((mod_(a, m)), d))));
	let temp_54_1 = (add_((add_((mod_(a, m)), d)), (sub_(c, a))));
	assert(eq_(temp_54_0, temp_54_1)) by {
		lemma_add_comm(sub_(c, a), add_(mod_(a, m), d));
	}
	let temp_55_0 = (mul_((mul_(d, b)), (add_(c, b))));
	let temp_55_1 = (mul_((mul_(b, d)), (add_(c, b))));
	assert(eq_(temp_55_0, temp_55_1)) by {
		cong_mul_(mul_(d, b), add_(c, b), mul_(b, d), add_(c, b));
		lemma_mul_comm(d, b);
		lemma_eq_ref(add_(c, b));
	}
	let temp_56_0 = (mul_((mul_(a, b)), (mul_(d, b))));
	let temp_56_1 = (mul_((mul_(d, b)), (mul_(a, b))));
	assert(eq_(temp_56_0, temp_56_1)) by {
		lemma_mul_comm(mul_(a, b), mul_(d, b));
	}
	let temp_57_0 = (mul_((mul_(d, d)), (add_((mod_(d, m)), a))));
	let temp_57_1 = (mul_((mul_(d, d)), (add_((mod_((sub_(d, (mul_((mul_((mul_(d, d)), (mul_(b, b)))), m)))), m)), a))));
	assert(eq_(temp_57_0, temp_57_1)) by {
		lemma_mul_comm(d, d);
		lemma_mod_mul_vanish(d, mul_(mul_(d, d), mul_(b, b)), m);
		cong_mul_(mul_(d, d), add_(mod_(d, m), a), mul_(d, d), add_(mod_(sub_(d, mul_(mul_(mul_(d, d), mul_(b, b)), m)), m), a));
		lemma_eq_ref(a);
		cong_add_(mod_(d, m), a, mod_(sub_(d, mul_(mul_(mul_(d, d), mul_(b, b)), m)), m), a);
	}
	let temp_58_0 = (mul_((mul_(a, (mod_(b, m)))), (mul_(c, d))));
	let temp_58_1 = (mul_((mul_((mod_(b, m)), a)), (mul_(c, d))));
	assert(eq_(temp_58_0, temp_58_1)) by {
		lemma_mul_comm(a, mod_(b, m));
		cong_mul_(mul_(a, mod_(b, m)), mul_(c, d), mul_(mod_(b, m), a), mul_(c, d));
		lemma_eq_ref(mul_(c, d));
	}
	let temp_59_0 = (mul_((mul_(a, c)), (mul_((mod_(d, m)), d))));
	let temp_59_1 = (mul_((mul_((mul_(a, c)), (mod_(d, m)))), d));
	assert(eq_(temp_59_0, temp_59_1)) by {
		lemma_mul_assoc(mul_(a, c), mod_(d, m), d);
	}
	let temp_60_0 = (mul_((mul_(b, a)), (sub_(c, a))));
	let temp_60_1 = (mul_(b, (mul_(a, (sub_(c, a))))));
	assert(eq_(temp_60_0, temp_60_1)) by {
		lemma_eq_sym(temp_60_1, temp_60_0);
		lemma_mul_assoc(b, a, sub_(c, a));
	}
	let temp_61_0 = (mul_((mul_(d, d)), (mul_(c, c))));
	let temp_61_1 = (mul_(d, (mul_(d, (mul_(c, c))))));
	assert(eq_(temp_61_0, temp_61_1)) by {
		lemma_eq_sym(temp_61_1, temp_61_0);
		lemma_mul_assoc(d, d, mul_(c, c));
	}
	let temp_62_0 = (mod_((mul_((mod_((mul_(b, c)), m)), (mul_(a, c)))), m));
	let temp_62_1 = (mod_((mul_((mod_((mul_(c, b)), m)), (mul_(a, c)))), m));
	assert(eq_(temp_62_0, temp_62_1)) by {
		lemma_mul_comm(b, c);
		cong_mod_(mul_(mod_(mul_(b, c), m), mul_(a, c)), m, mul_(mod_(mul_(c, b), m), mul_(a, c)), m);
		cong_mul_(mod_(mul_(b, c), m), mul_(a, c), mod_(mul_(c, b), m), mul_(a, c));
		lemma_eq_ref(m);
		lemma_eq_ref(mul_(a, c));
		cong_mod_(mul_(b, c), m, mul_(c, b), m);
	}
	let temp_63_0 = (add_((mul_(c, a)), (mul_(c, a))));
	let temp_63_1 = (mul_((add_(c, c)), a));
	assert(eq_(temp_63_0, temp_63_1)) by {
		lemma_eq_sym(temp_63_1, temp_63_0);
		lemma_mul_dist(c, c, a);
	}
	let temp_64_0 = (mod_((mul_((mod_((mul_(b, c)), m)), (mod_((mul_((mod_(d, m)), c)), m)))), m));
	let temp_64_1 = (mod_((mod_((mul_((mod_((mul_(b, c)), m)), (mul_((mod_(d, m)), c)))), m)), m));
	assert(eq_(temp_64_0, temp_64_1)) by {
		lemma_mod_mul_noop(mod_(mul_(b, c), m), mul_(mod_(d, m), c), m);
		lemma_eq_sym(temp_64_1, temp_64_0);
	}
	let temp_65_0 = (add_((mul_(d, b)), (mul_(a, (mod_(c, m))))));
	let temp_65_1 = (add_((mul_(d, b)), (mul_(a, (mod_((add_((mul_((mul_((mul_(c, a)), (mod_((mul_((mod_(d, m)), b)), m)))), m)), c)), m))))));
	assert(eq_(temp_65_0, temp_65_1)) by {
		lemma_eq_ref(mul_(d, b));
		cong_mul_(a, mod_(c, m), a, mod_(add_(mul_(mul_(mul_(c, a), mod_(mul_(mod_(d, m), b), m)), m), c), m));
		lemma_eq_ref(a);
		lemma_mod_mul_vanish(c, mul_(mul_(c, a), mod_(mul_(mod_(d, m), b), m)), m);
		cong_add_(mul_(d, b), mul_(a, mod_(c, m)), mul_(d, b), mul_(a, mod_(add_(mul_(mul_(mul_(c, a), mod_(mul_(mod_(d, m), b), m)), m), c), m)));
	}
	let temp_66_0 = (mul_((add_(b, b)), (mul_(b, d))));
	let temp_66_1 = (add_((mul_(b, (mul_(b, d)))), (mul_(b, (mul_(b, d))))));
	assert(eq_(temp_66_0, temp_66_1)) by {
		lemma_mul_dist(b, b, mul_(b, d));
	}
	let temp_67_0 = (mod_((mul_((mul_(b, a)), (add_(b, a)))), m));
	let temp_67_1 = (mod_((add_((mul_((mul_(b, a)), b)), (mul_((mul_(b, a)), a)))), m));
	assert(eq_(temp_67_0, temp_67_1)) by {
		lemma_mul_dist(mul_(b, a), b, a);
		cong_mod_(mul_(mul_(b, a), add_(b, a)), m, add_(mul_(mul_(b, a), b), mul_(mul_(b, a), a)), m);
		lemma_eq_ref(m);
	}
	let temp_68_0 = (mul_((mod_((mul_(a, c)), m)), (mul_(b, b))));
	let temp_68_1 = (mul_((mod_((mul_(c, a)), m)), (mul_(b, b))));
	assert(eq_(temp_68_0, temp_68_1)) by {
		cong_mod_(mul_(a, c), m, mul_(c, a), m);
		lemma_mul_comm(a, c);
		lemma_mul_comm(b, b);
		cong_mul_(mod_(mul_(a, c), m), mul_(b, b), mod_(mul_(c, a), m), mul_(b, b));
		lemma_eq_ref(m);
	}
	let temp_69_0 = (mul_((mod_((add_(a, b)), m)), (mod_((mul_((mod_(b, m)), d)), m))));
	let temp_69_1 = (mul_((mod_((add_(a, b)), m)), (mod_((add_((mul_((mul_((mul_(c, c)), (mul_(d, (mod_(d, m)))))), m)), (mul_((mod_(b, m)), d)))), m))));
	assert(eq_(temp_69_0, temp_69_1)) by {
		lemma_mod_mul_vanish(mul_(mod_(b, m), d), mul_(mul_(c, c), mul_(d, mod_(d, m))), m);
		cong_mul_(mod_(add_(a, b), m), mod_(mul_(mod_(b, m), d), m), mod_(add_(a, b), m), mod_(add_(mul_(mul_(mul_(c, c), mul_(d, mod_(d, m))), m), mul_(mod_(b, m), d)), m));
		lemma_eq_ref(mod_(add_(a, b), m));
	}
	let temp_70_0 = (mul_((mod_((mul_(c, d)), m)), (mul_(as_elem(82), b))));
	let temp_70_1 = (mul_((mod_((mul_(c, d)), m)), (mul_(b, as_elem(82)))));
	assert(eq_(temp_70_0, temp_70_1)) by {
		lemma_mul_comm(as_elem(82), b);
		cong_mul_(mod_(mul_(c, d), m), mul_(as_elem(82), b), mod_(mul_(c, d), m), mul_(b, as_elem(82)));
		lemma_eq_ref(mod_(mul_(c, d), m));
	}
	let temp_71_0 = (sub_((mul_(c, b)), (mul_(c, a))));
	let temp_71_1 = (sub_((mul_(b, c)), (mul_(c, a))));
	assert(eq_(temp_71_0, temp_71_1)) by {
		cong_sub_(mul_(c, b), mul_(c, a), mul_(b, c), mul_(c, a));
		lemma_mul_comm(c, b);
		lemma_eq_ref(mul_(c, a));
	}
	let temp_72_0 = (mul_((mul_(a, c)), (mul_(c, c))));
	let temp_72_1 = (mul_((mul_(c, a)), (mul_(c, c))));
	assert(eq_(temp_72_0, temp_72_1)) by {
		cong_mul_(mul_(a, c), mul_(c, c), mul_(c, a), mul_(c, c));
		lemma_mul_comm(a, c);
		lemma_mul_comm(c, c);
	}
	let temp_73_0 = (mul_((mul_(c, c)), (mul_(b, a))));
	let temp_73_1 = (mul_((mul_(c, c)), (mul_(b, a))));
	assert(eq_(temp_73_0, temp_73_1)) by {
		lemma_eq_ref(temp_73_0);
	}
	let temp_74_0 = (mul_((mul_(a, b)), (sub_(d, b))));
	let temp_74_1 = (mul_(a, (mul_(b, (sub_(d, b))))));
	assert(eq_(temp_74_0, temp_74_1)) by {
		lemma_eq_sym(temp_74_1, temp_74_0);
		lemma_mul_assoc(a, b, sub_(d, b));
	}
	let temp_75_0 = (mul_((mul_((mod_(a, m)), c)), (mul_(d, b))));
	let temp_75_1 = (mul_((mul_((mod_((add_(a, (mul_((mul_((mod_((mul_((mod_(a, m)), a)), m)), (mul_(a, c)))), m)))), m)), c)), (mul_(d, b))));
	assert(eq_(temp_75_0, temp_75_1)) by {
		lemma_mod_mul_vanish(a, mul_(mod_(mul_(mod_(a, m), a), m), mul_(a, c)), m);
		cong_mul_(mul_(mod_(a, m), c), mul_(d, b), mul_(mod_(add_(a, mul_(mul_(mod_(mul_(mod_(a, m), a), m), mul_(a, c)), m)), m), c), mul_(d, b));
		lemma_eq_ref(c);
		cong_mul_(mod_(a, m), c, mod_(add_(a, mul_(mul_(mod_(mul_(mod_(a, m), a), m), mul_(a, c)), m)), m), c);
		lemma_eq_ref(mul_(d, b));
	}
	let temp_76_0 = (mul_((mul_(d, c)), d));
	let temp_76_1 = (mul_(d, (mul_(c, d))));
	assert(eq_(temp_76_0, temp_76_1)) by {
		lemma_eq_sym(temp_76_1, temp_76_0);
		lemma_mul_assoc(d, c, d);
	}
	let temp_77_0 = (mul_((mul_(d, b)), c));
	let temp_77_1 = (mul_(d, (mul_(b, c))));
	assert(eq_(temp_77_0, temp_77_1)) by {
		lemma_eq_sym(temp_77_1, temp_77_0);
		lemma_mul_assoc(d, b, c);
	}
	let temp_78_0 = (mul_((mul_(a, a)), (mul_(c, d))));
	let temp_78_1 = (mul_((mul_((mul_(a, a)), c)), d));
	assert(eq_(temp_78_0, temp_78_1)) by {
		lemma_mul_assoc(mul_(a, a), c, d);
	}
	let temp_79_0 = (mul_((mul_(b, c)), (mod_((mul_(b, d)), m))));
	let temp_79_1 = (mul_((mul_(b, c)), (mod_((mul_(d, b)), m))));
	assert(eq_(temp_79_0, temp_79_1)) by {
		lemma_mul_comm(d, b);
		cong_mul_(mul_(b, c), mod_(mul_(b, d), m), mul_(b, c), mod_(mul_(d, b), m));
		lemma_eq_ref(mul_(b, c));
		lemma_eq_sym(mod_(mul_(d, b), m), mod_(mul_(b, d), m));
		cong_mod_(mul_(d, b), m, mul_(b, d), m);
		lemma_eq_ref(m);
	}

}

} // verus!