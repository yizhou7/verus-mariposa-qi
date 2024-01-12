use builtin_macros::*;
// use builtin::*;
mod nl_basics;
use crate::nl_basics::*;
verus! {

pub proof fn free_0(a: Elem, b: Elem, c: Elem, d: Elem, m: Elem)
{
	let temp_0_0 = (mul_((add_(a, d)), (mul_((mod_(c, m)), c))));
	let temp_0_1 = (mul_((mul_((add_(a, d)), (mod_(c, m)))), c));
	assert(eq_(temp_0_0, temp_0_1)) by {
		lemma_mul_assoc(add_(a, d), mod_(c, m), c);
	}
	let temp_1_0 = (mul_((mod_((mul_(c, c)), m)), (add_(d, c))));
	let temp_1_1 = (mul_((mod_((mul_(c, c)), m)), (add_(d, c))));
	assert(eq_(temp_1_0, temp_1_1)) by {
		lemma_eq_ref(temp_1_0);
	}
	let temp_2_0 = (mul_((add_(d, (mod_(c, m)))), (mul_(b, d))));
	let temp_2_1 = (mul_((mul_(b, d)), (add_(d, (mod_(c, m))))));
	assert(eq_(temp_2_0, temp_2_1)) by {
		lemma_mul_comm(add_(d, mod_(c, m)), mul_(b, d));
	}
	let temp_3_0 = (mul_((mul_(d, a)), (mul_(a, a))));
	let temp_3_1 = (mul_((mul_(a, d)), (mul_(a, a))));
	assert(eq_(temp_3_0, temp_3_1)) by {
		cong_mul_(mul_(d, a), mul_(a, a), mul_(a, d), mul_(a, a));
		lemma_mul_comm(d, a);
		lemma_mul_comm(a, a);
	}
	let temp_4_0 = (sub_((mul_(as_elem(2), a)), (mul_((mod_(a, m)), c))));
	let temp_4_1 = (sub_((mul_(as_elem(2), a)), (mul_((mod_((add_(a, (mul_((mod_((mul_((mul_(as_elem(40), a)), (mul_(b, (mod_(d, m)))))), m)), m)))), m)), c))));
	assert(eq_(temp_4_0, temp_4_1)) by {
		lemma_eq_ref(c);
		cong_sub_(mul_(as_elem(2), a), mul_(mod_(a, m), c), mul_(as_elem(2), a), mul_(mod_(add_(a, mul_(mod_(mul_(mul_(as_elem(40), a), mul_(b, mod_(d, m))), m), m)), m), c));
		lemma_mod_mul_vanish(a, mod_(mul_(mul_(as_elem(40), a), mul_(b, mod_(d, m))), m), m);
		lemma_eq_ref(mul_(as_elem(2), a));
		cong_mul_(mod_(a, m), c, mod_(add_(a, mul_(mod_(mul_(mul_(as_elem(40), a), mul_(b, mod_(d, m))), m), m)), m), c);
	}
	let temp_5_0 = (mul_((mul_(c, a)), a));
	let temp_5_1 = (mul_(c, (mul_(a, a))));
	assert(eq_(temp_5_0, temp_5_1)) by {
		lemma_eq_sym(temp_5_1, temp_5_0);
		lemma_mul_assoc(c, a, a);
	}
	let temp_6_0 = (add_((add_(b, a)), (mul_(a, d))));
	let temp_6_1 = (add_((add_(b, a)), (mul_(d, a))));
	assert(eq_(temp_6_0, temp_6_1)) by {
		cong_add_(add_(b, a), mul_(a, d), add_(b, a), mul_(d, a));
		lemma_mul_comm(a, d);
		lemma_eq_ref(add_(b, a));
	}
	let temp_7_0 = (mul_((mul_(d, d)), (mul_(d, a))));
	let temp_7_1 = (mul_((mul_(d, d)), (mul_(d, a))));
	assert(eq_(temp_7_0, temp_7_1)) by {
		lemma_eq_ref(temp_7_0);
	}
	let temp_8_0 = (mul_((mul_(d, d)), (mul_((mod_(a, m)), c))));
	let temp_8_1 = (mul_((mul_(d, d)), (mul_((mod_((add_(a, (mul_((mul_((mul_(d, d)), (mul_(as_elem(43), b)))), m)))), m)), c))));
	assert(eq_(temp_8_0, temp_8_1)) by {
		lemma_mul_comm(d, d);
		lemma_mod_mul_vanish(a, mul_(mul_(d, d), mul_(as_elem(43), b)), m);
		cong_mul_(mul_(d, d), mul_(mod_(a, m), c), mul_(d, d), mul_(mod_(add_(a, mul_(mul_(mul_(d, d), mul_(as_elem(43), b)), m)), m), c));
		lemma_eq_ref(c);
		cong_mul_(mod_(a, m), c, mod_(add_(a, mul_(mul_(mul_(d, d), mul_(as_elem(43), b)), m)), m), c);
	}
	let temp_9_0 = (mul_((sub_(c, b)), (mul_(d, b))));
	let temp_9_1 = (mul_((sub_(c, b)), (mul_(b, d))));
	assert(eq_(temp_9_0, temp_9_1)) by {
		cong_mul_(sub_(c, b), mul_(d, b), sub_(c, b), mul_(b, d));
		lemma_mul_comm(d, b);
		lemma_eq_ref(sub_(c, b));
	}
	let temp_10_0 = (mul_((mul_(a, b)), (mul_((mod_(b, m)), a))));
	let temp_10_1 = (mul_((mul_((mul_(a, b)), (mod_(b, m)))), a));
	assert(eq_(temp_10_0, temp_10_1)) by {
		lemma_mul_assoc(mul_(a, b), mod_(b, m), a);
	}
	let temp_11_0 = (mod_((mul_((mul_(a, b)), (mul_((mod_(c, m)), c)))), m));
	let temp_11_1 = (mod_((mul_((mul_(a, b)), (mul_((mod_((add_((mul_((mod_((mul_((mul_((mod_(a, m)), c)), (mul_(c, (mod_(c, m)))))), m)), m)), c)), m)), c)))), m));
	assert(eq_(temp_11_0, temp_11_1)) by {
		lemma_mod_mul_vanish(c, mod_(mul_(mul_(mod_(a, m), c), mul_(c, mod_(c, m))), m), m);
		cong_mod_(mul_(mul_(a, b), mul_(mod_(c, m), c)), m, mul_(mul_(a, b), mul_(mod_(add_(mul_(mod_(mul_(mul_(mod_(a, m), c), mul_(c, mod_(c, m))), m), m), c), m), c)), m);
		lemma_eq_ref(mul_(a, b));
		lemma_eq_ref(c);
		cong_mul_(mod_(c, m), c, mod_(add_(mul_(mod_(mul_(mul_(mod_(a, m), c), mul_(c, mod_(c, m))), m), m), c), m), c);
		cong_mul_(mul_(a, b), mul_(mod_(c, m), c), mul_(a, b), mul_(mod_(add_(mul_(mod_(mul_(mul_(mod_(a, m), c), mul_(c, mod_(c, m))), m), m), c), m), c));
		lemma_eq_ref(m);
	}
	let temp_12_0 = (mul_((sub_(d, d)), (mul_(c, (mod_(d, m))))));
	let temp_12_1 = (mul_((mul_((sub_(d, d)), c)), (mod_(d, m))));
	assert(eq_(temp_12_0, temp_12_1)) by {
		lemma_mul_assoc(sub_(d, d), c, mod_(d, m));
	}
	let temp_13_0 = (mul_((mod_((mul_(a, a)), m)), (mul_(b, c))));
	let temp_13_1 = (mul_((mul_(b, c)), (mod_((mul_(a, a)), m))));
	assert(eq_(temp_13_0, temp_13_1)) by {
		lemma_mul_comm(mod_(mul_(a, a), m), mul_(b, c));
	}
	let temp_14_0 = (mul_((mul_(d, c)), (mul_(b, b))));
	let temp_14_1 = (mul_((mul_(c, d)), (mul_(b, b))));
	assert(eq_(temp_14_0, temp_14_1)) by {
		cong_mul_(mul_(d, c), mul_(b, b), mul_(c, d), mul_(b, b));
		lemma_mul_comm(d, c);
		lemma_mul_comm(b, b);
	}
	let temp_15_0 = (mul_((mul_(d, a)), (mul_(d, a))));
	let temp_15_1 = (mul_((mul_(d, a)), (mul_(d, a))));
	assert(eq_(temp_15_0, temp_15_1)) by {
		lemma_eq_ref(temp_15_0);
	}
	let temp_16_0 = (mul_((add_(a, d)), (mul_(c, a))));
	let temp_16_1 = (mul_((add_(d, a)), (mul_(c, a))));
	assert(eq_(temp_16_0, temp_16_1)) by {
		cong_mul_(add_(a, d), mul_(c, a), add_(d, a), mul_(c, a));
		lemma_add_comm(a, d);
		lemma_eq_ref(mul_(c, a));
	}
	let temp_17_0 = (mul_((mod_((add_(d, c)), m)), (mod_((add_(d, d)), m))));
	let temp_17_1 = (mul_((mod_((add_(d, d)), m)), (mod_((add_(d, c)), m))));
	assert(eq_(temp_17_0, temp_17_1)) by {
		lemma_mul_comm(mod_(add_(d, c), m), mod_(add_(d, d), m));
	}
	let temp_18_0 = (mul_(c, (add_(d, c))));
	let temp_18_1 = (add_((mul_(c, d)), (mul_(c, c))));
	assert(eq_(temp_18_0, temp_18_1)) by {
		lemma_mul_dist(c, d, c);
	}
	let temp_19_0 = (mul_((mul_(d, c)), (add_(a, d))));
	let temp_19_1 = (mul_(d, (mul_(c, (add_(a, d))))));
	assert(eq_(temp_19_0, temp_19_1)) by {
		lemma_eq_sym(temp_19_1, temp_19_0);
		lemma_mul_assoc(d, c, add_(a, d));
	}
	let temp_20_0 = (mul_((mul_(as_elem(22), b)), (mul_(c, d))));
	let temp_20_1 = (mul_((mul_((mul_(as_elem(22), b)), c)), d));
	assert(eq_(temp_20_0, temp_20_1)) by {
		lemma_mul_assoc(mul_(as_elem(22), b), c, d);
	}
	let temp_21_0 = (mod_((mul_((mod_((mul_(b, d)), m)), (mod_((mul_(d, b)), m)))), m));
	let temp_21_1 = (mod_((mul_((mod_((add_((mul_((mul_((mul_(d, d)), (mul_(a, c)))), m)), (mul_(b, d)))), m)), (mod_((mul_(d, b)), m)))), m));
	assert(eq_(temp_21_0, temp_21_1)) by {
		lemma_mod_mul_vanish(mul_(b, d), mul_(mul_(d, d), mul_(a, c)), m);
		cong_mod_(mul_(mod_(mul_(b, d), m), mod_(mul_(d, b), m)), m, mul_(mod_(add_(mul_(mul_(mul_(d, d), mul_(a, c)), m), mul_(b, d)), m), mod_(mul_(d, b), m)), m);
		lemma_eq_ref(m);
		lemma_eq_ref(mod_(mul_(d, b), m));
		cong_mul_(mod_(mul_(b, d), m), mod_(mul_(d, b), m), mod_(add_(mul_(mul_(mul_(d, d), mul_(a, c)), m), mul_(b, d)), m), mod_(mul_(d, b), m));
	}
	let temp_22_0 = (mul_((mul_(a, d)), (mul_(d, a))));
	let temp_22_1 = (mul_((mul_(d, a)), (mul_(a, d))));
	assert(eq_(temp_22_0, temp_22_1)) by {
		lemma_mul_comm(mul_(a, d), mul_(d, a));
	}
	let temp_23_0 = (mul_((mul_(c, b)), (sub_(a, (mod_(b, m))))));
	let temp_23_1 = (mul_((sub_(a, (mod_(b, m)))), (mul_(c, b))));
	assert(eq_(temp_23_0, temp_23_1)) by {
		lemma_mul_comm(mul_(c, b), sub_(a, mod_(b, m)));
	}
	let temp_24_0 = (mul_((mul_(b, c)), (mul_(c, c))));
	let temp_24_1 = (mul_((mul_((mul_(b, c)), c)), c));
	assert(eq_(temp_24_0, temp_24_1)) by {
		lemma_mul_assoc(mul_(b, c), c, c);
	}
	let temp_25_0 = (mul_((mul_(d, c)), (mul_(as_elem(51), a))));
	let temp_25_1 = (mul_(d, (mul_(c, (mul_(as_elem(51), a))))));
	assert(eq_(temp_25_0, temp_25_1)) by {
		lemma_mul_assoc(d, c, mul_(as_elem(51), a));
		lemma_eq_sym(temp_25_1, temp_25_0);
	}
	let temp_26_0 = (mul_((mul_(a, b)), (mul_(c, (mod_(d, m))))));
	let temp_26_1 = (mul_(a, (mul_(b, (mul_(c, (mod_(d, m))))))));
	assert(eq_(temp_26_0, temp_26_1)) by {
		lemma_mul_assoc(a, b, mul_(c, mod_(d, m)));
		lemma_eq_sym(temp_26_1, temp_26_0);
	}
	let temp_27_0 = (mul_((mul_(b, c)), (mul_(b, c))));
	let temp_27_1 = (mul_((mul_(b, c)), (mul_(b, c))));
	assert(eq_(temp_27_0, temp_27_1)) by {
		lemma_eq_ref(temp_27_0);
	}
	let temp_28_0 = (mul_((mul_(d, d)), (add_(a, a))));
	let temp_28_1 = (mul_((add_(a, a)), (mul_(d, d))));
	assert(eq_(temp_28_0, temp_28_1)) by {
		lemma_mul_comm(mul_(d, d), add_(a, a));
	}
	let temp_29_0 = (mod_((sub_((mul_(b, (mod_(d, m)))), (mul_(d, a)))), m));
	let temp_29_1 = (mod_((sub_((mod_((mul_(b, (mod_(d, m)))), m)), (mul_(d, a)))), m));
	assert(eq_(temp_29_0, temp_29_1)) by {
		lemma_mod_sub_noop(mul_(b, mod_(d, m)), mul_(d, a), m);
	}
	let temp_30_0 = (mul_((mul_(b, d)), (mul_(b, d))));
	let temp_30_1 = (mul_((mul_((mul_(b, d)), b)), d));
	assert(eq_(temp_30_0, temp_30_1)) by {
		lemma_mul_assoc(mul_(b, d), b, d);
	}
	let temp_31_0 = (mod_((mul_((mul_(b, c)), (mul_(c, c)))), m));
	let temp_31_1 = (mod_((add_((mul_((mul_(b, c)), (mul_(c, c)))), (mul_((mul_((mul_(d, c)), (mul_((mod_(d, m)), (mod_(b, m)))))), m)))), m));
	assert(eq_(temp_31_0, temp_31_1)) by {
		lemma_mod_mul_vanish(mul_(mul_(b, c), mul_(c, c)), mul_(mul_(d, c), mul_(mod_(d, m), mod_(b, m))), m);
	}
	let temp_32_0 = (mul_((mul_(d, b)), (sub_(a, a))));
	let temp_32_1 = (mul_((mul_(b, d)), (sub_(a, a))));
	assert(eq_(temp_32_0, temp_32_1)) by {
		cong_mul_(mul_(d, b), sub_(a, a), mul_(b, d), sub_(a, a));
		lemma_mul_comm(d, b);
		lemma_eq_ref(sub_(a, a));
	}
	let temp_33_0 = (mul_((mul_(b, c)), (mul_(c, d))));
	let temp_33_1 = (mul_(b, (mul_(c, (mul_(c, d))))));
	assert(eq_(temp_33_0, temp_33_1)) by {
		lemma_eq_sym(temp_33_1, temp_33_0);
		lemma_mul_assoc(b, c, mul_(c, d));
	}
	let temp_34_0 = (mul_((mul_(b, d)), (mul_(a, d))));
	let temp_34_1 = (mul_(b, (mul_(d, (mul_(a, d))))));
	assert(eq_(temp_34_0, temp_34_1)) by {
		lemma_eq_sym(temp_34_1, temp_34_0);
		lemma_mul_assoc(b, d, mul_(a, d));
	}
	let temp_35_0 = (mul_((mul_(b, b)), (mul_(c, a))));
	let temp_35_1 = (mul_((mul_(b, b)), (mul_(c, a))));
	assert(eq_(temp_35_0, temp_35_1)) by {
		lemma_eq_ref(temp_35_0);
	}
	let temp_36_0 = (mul_((mul_((mod_(d, m)), b)), (mul_(c, d))));
	let temp_36_1 = (mul_((mod_(d, m)), (mul_(b, (mul_(c, d))))));
	assert(eq_(temp_36_0, temp_36_1)) by {
		lemma_mul_assoc(mod_(d, m), b, mul_(c, d));
		lemma_eq_sym(temp_36_1, temp_36_0);
	}
	let temp_37_0 = (sub_((mul_(a, a)), (mul_((mod_(a, m)), a))));
	let temp_37_1 = (mul_((sub_(a, (mod_(a, m)))), a));
	assert(eq_(temp_37_0, temp_37_1)) by {
		lemma_eq_sym(temp_37_1, temp_37_0);
		lemma_mul_dist(a, a, mod_(a, m));
	}
	let temp_38_0 = (mul_((mul_(b, b)), (mul_(c, c))));
	let temp_38_1 = (mul_((mul_(b, b)), (mul_(c, c))));
	assert(eq_(temp_38_0, temp_38_1)) by {
		lemma_eq_ref(temp_38_0);
	}
	let temp_39_0 = (mul_((mul_(a, b)), (mul_(c, d))));
	let temp_39_1 = (mul_((mul_((mul_(a, b)), c)), d));
	assert(eq_(temp_39_0, temp_39_1)) by {
		lemma_mul_assoc(mul_(a, b), c, d);
	}
	let temp_40_0 = (mod_((mul_((sub_((mod_(b, m)), d)), b)), m));
	let temp_40_1 = (mod_((sub_((mul_((mod_(b, m)), b)), (mul_(d, b)))), m));
	assert(eq_(temp_40_0, temp_40_1)) by {
		lemma_mul_dist(b, mod_(b, m), d);
		cong_mod_(mul_(sub_(mod_(b, m), d), b), m, sub_(mul_(mod_(b, m), b), mul_(d, b)), m);
		lemma_eq_ref(m);
	}
	let temp_41_0 = (mul_((mul_(as_elem(76), d)), (mod_((mul_(as_elem(67), b)), m))));
	let temp_41_1 = (mul_(as_elem(76), (mul_(d, (mod_((mul_(as_elem(67), b)), m))))));
	assert(eq_(temp_41_0, temp_41_1)) by {
		lemma_mul_assoc(as_elem(76), d, mod_(mul_(as_elem(67), b), m));
		lemma_eq_sym(temp_41_1, temp_41_0);
	}
	let temp_42_0 = (mul_((mul_(a, b)), (mul_(a, c))));
	let temp_42_1 = (mul_(a, (mul_(b, (mul_(a, c))))));
	assert(eq_(temp_42_0, temp_42_1)) by {
		lemma_eq_sym(temp_42_1, temp_42_0);
		lemma_mul_assoc(a, b, mul_(a, c));
	}
	let temp_43_0 = (add_((sub_(c, d)), (add_(a, b))));
	let temp_43_1 = (add_((add_(a, b)), (sub_(c, d))));
	assert(eq_(temp_43_0, temp_43_1)) by {
		lemma_add_comm(sub_(c, d), add_(a, b));
	}
	let temp_44_0 = (mul_((add_(b, d)), (mul_(c, (mod_(b, m))))));
	let temp_44_1 = (mul_((add_(b, d)), (mul_((mod_(b, m)), c))));
	assert(eq_(temp_44_0, temp_44_1)) by {
		lemma_mul_comm(c, mod_(b, m));
		cong_mul_(add_(b, d), mul_(c, mod_(b, m)), add_(b, d), mul_(mod_(b, m), c));
		lemma_eq_ref(add_(b, d));
	}
	let temp_45_0 = (mod_((sub_((mul_(a, d)), (mul_(b, d)))), m));
	let temp_45_1 = (mod_((mul_((sub_(a, b)), d)), m));
	assert(eq_(temp_45_0, temp_45_1)) by {
		lemma_mul_dist(d, a, b);
		cong_mod_(sub_(mul_(a, d), mul_(b, d)), m, mul_(sub_(a, b), d), m);
		lemma_eq_sym(mul_(sub_(a, b), d), sub_(mul_(a, d), mul_(b, d)));
		lemma_eq_ref(m);
	}
	let temp_46_0 = (mul_((add_((mod_(b, m)), c)), (mul_(b, d))));
	let temp_46_1 = (add_((mul_((mod_(b, m)), (mul_(b, d)))), (mul_(c, (mul_(b, d))))));
	assert(eq_(temp_46_0, temp_46_1)) by {
		lemma_mul_dist(mod_(b, m), c, mul_(b, d));
	}
	let temp_47_0 = (mod_((mul_((add_(d, c)), (mul_(c, d)))), m));
	let temp_47_1 = (mod_((mul_((add_(c, d)), (mul_(c, d)))), m));
	assert(eq_(temp_47_0, temp_47_1)) by {
		lemma_add_comm(d, c);
		cong_mod_(mul_(add_(d, c), mul_(c, d)), m, mul_(add_(c, d), mul_(c, d)), m);
		lemma_eq_ref(mul_(c, d));
		cong_mul_(add_(d, c), mul_(c, d), add_(c, d), mul_(c, d));
		lemma_eq_ref(m);
	}
	let temp_48_0 = (mul_((mul_(d, c)), (mul_(a, a))));
	let temp_48_1 = (mul_(d, (mul_(c, (mul_(a, a))))));
	assert(eq_(temp_48_0, temp_48_1)) by {
		lemma_eq_sym(temp_48_1, temp_48_0);
		lemma_mul_assoc(d, c, mul_(a, a));
	}
	let temp_49_0 = (sub_(a, (mul_(a, b))));
	let temp_49_1 = (sub_(a, (mul_(b, a))));
	assert(eq_(temp_49_0, temp_49_1)) by {
		cong_sub_(a, mul_(a, b), a, mul_(b, a));
		lemma_mul_comm(a, b);
		lemma_eq_ref(a);
	}
	let temp_50_0 = (mul_((mul_((mod_(a, m)), (mod_(c, m)))), (add_(c, a))));
	let temp_50_1 = (add_((mul_((mul_((mod_(a, m)), (mod_(c, m)))), c)), (mul_((mul_((mod_(a, m)), (mod_(c, m)))), a))));
	assert(eq_(temp_50_0, temp_50_1)) by {
		lemma_mul_dist(mul_(mod_(a, m), mod_(c, m)), c, a);
	}
	let temp_51_0 = (sub_((mul_(b, (mod_(a, m)))), (mul_((mod_(d, m)), a))));
	let temp_51_1 = (sub_((mul_(b, (mod_(a, m)))), (mul_(a, (mod_(d, m))))));
	assert(eq_(temp_51_0, temp_51_1)) by {
		lemma_mul_comm(mod_(d, m), a);
		cong_sub_(mul_(b, mod_(a, m)), mul_(mod_(d, m), a), mul_(b, mod_(a, m)), mul_(a, mod_(d, m)));
		lemma_eq_ref(mul_(b, mod_(a, m)));
	}
	let temp_52_0 = (mul_((mul_(a, d)), (mul_(a, b))));
	let temp_52_1 = (mul_((mul_(a, b)), (mul_(a, d))));
	assert(eq_(temp_52_0, temp_52_1)) by {
		lemma_mul_comm(mul_(a, d), mul_(a, b));
	}
	let temp_53_0 = (mul_((mul_(b, c)), (mul_(d, d))));
	let temp_53_1 = (mul_((mul_(c, b)), (mul_(d, d))));
	assert(eq_(temp_53_0, temp_53_1)) by {
		cong_mul_(mul_(b, c), mul_(d, d), mul_(c, b), mul_(d, d));
		lemma_mul_comm(b, c);
		lemma_mul_comm(d, d);
	}
	let temp_54_0 = (add_((sub_(b, d)), (mul_(a, b))));
	let temp_54_1 = (add_((sub_(b, d)), (mul_(b, a))));
	assert(eq_(temp_54_0, temp_54_1)) by {
		cong_add_(sub_(b, d), mul_(a, b), sub_(b, d), mul_(b, a));
		lemma_mul_comm(a, b);
		lemma_eq_ref(sub_(b, d));
	}
	let temp_55_0 = (mul_((mul_(b, a)), (mul_(b, d))));
	let temp_55_1 = (mul_((mul_((mul_(b, a)), b)), d));
	assert(eq_(temp_55_0, temp_55_1)) by {
		lemma_mul_assoc(mul_(b, a), b, d);
	}
	let temp_56_0 = (mul_((mul_(b, c)), (mul_(b, b))));
	let temp_56_1 = (mul_(b, (mul_(c, (mul_(b, b))))));
	assert(eq_(temp_56_0, temp_56_1)) by {
		lemma_eq_sym(temp_56_1, temp_56_0);
		lemma_mul_assoc(b, c, mul_(b, b));
	}
	let temp_57_0 = (mul_((mod_((mul_(b, c)), m)), (mul_(c, a))));
	let temp_57_1 = (mul_((mod_((add_((mul_(b, c)), (mul_((mul_((mod_((sub_(b, a)), m)), (mul_(b, c)))), m)))), m)), (mul_(c, a))));
	assert(eq_(temp_57_0, temp_57_1)) by {
		lemma_mod_mul_vanish(mul_(b, c), mul_(mod_(sub_(b, a), m), mul_(b, c)), m);
		cong_mul_(mod_(mul_(b, c), m), mul_(c, a), mod_(add_(mul_(b, c), mul_(mul_(mod_(sub_(b, a), m), mul_(b, c)), m)), m), mul_(c, a));
		lemma_eq_ref(mul_(c, a));
	}
	let temp_58_0 = (mul_((sub_(b, a)), (mul_((mod_(b, m)), a))));
	let temp_58_1 = (mul_((sub_(b, a)), (mul_(a, (mod_(b, m))))));
	assert(eq_(temp_58_0, temp_58_1)) by {
		cong_mul_(sub_(b, a), mul_(mod_(b, m), a), sub_(b, a), mul_(a, mod_(b, m)));
		lemma_mul_comm(mod_(b, m), a);
		lemma_eq_ref(sub_(b, a));
	}
	let temp_59_0 = (mul_((mul_(c, b)), (mul_(b, d))));
	let temp_59_1 = (mul_(c, (mul_(b, (mul_(b, d))))));
	assert(eq_(temp_59_0, temp_59_1)) by {
		lemma_eq_sym(temp_59_1, temp_59_0);
		lemma_mul_assoc(c, b, mul_(b, d));
	}
	let temp_60_0 = (sub_((mul_(d, d)), (mul_(c, c))));
	let temp_60_1 = (sub_((mul_(d, d)), (mul_(c, c))));
	assert(eq_(temp_60_0, temp_60_1)) by {
		lemma_eq_ref(temp_60_0);
	}
	let temp_61_0 = (mul_((mul_(a, a)), (mul_(b, c))));
	let temp_61_1 = (mul_((mul_((mul_(a, a)), b)), c));
	assert(eq_(temp_61_0, temp_61_1)) by {
		lemma_mul_assoc(mul_(a, a), b, c);
	}
	let temp_62_0 = (mul_((mul_(b, (mod_(c, m)))), (mul_((mod_(b, m)), c))));
	let temp_62_1 = (mul_((mul_((mod_(b, m)), c)), (mul_(b, (mod_(c, m))))));
	assert(eq_(temp_62_0, temp_62_1)) by {
		lemma_mul_comm(mul_(b, mod_(c, m)), mul_(mod_(b, m), c));
	}
	let temp_63_0 = (mul_((mul_(d, b)), (mul_(a, d))));
	let temp_63_1 = (mul_((mul_(b, d)), (mul_(a, d))));
	assert(eq_(temp_63_0, temp_63_1)) by {
		cong_mul_(mul_(d, b), mul_(a, d), mul_(b, d), mul_(a, d));
		lemma_mul_comm(d, b);
		lemma_eq_ref(mul_(a, d));
	}
	let temp_64_0 = (sub_((add_(c, b)), (mul_(c, d))));
	let temp_64_1 = (sub_((add_(b, c)), (mul_(c, d))));
	assert(eq_(temp_64_0, temp_64_1)) by {
		cong_sub_(add_(c, b), mul_(c, d), add_(b, c), mul_(c, d));
		lemma_add_comm(c, b);
		lemma_eq_ref(mul_(c, d));
	}
	let temp_65_0 = (mul_((mul_(a, b)), (mul_(a, a))));
	let temp_65_1 = (mul_((mul_((mul_(a, b)), a)), a));
	assert(eq_(temp_65_0, temp_65_1)) by {
		lemma_mul_assoc(mul_(a, b), a, a);
	}
	let temp_66_0 = (mul_((mul_(b, c)), (mul_(as_elem(62), a))));
	let temp_66_1 = (mul_((mul_(b, c)), (mul_(a, as_elem(62)))));
	assert(eq_(temp_66_0, temp_66_1)) by {
		lemma_mul_comm(as_elem(62), a);
		cong_mul_(mul_(b, c), mul_(as_elem(62), a), mul_(b, c), mul_(a, as_elem(62)));
		lemma_eq_ref(mul_(b, c));
	}
	let temp_67_0 = (mul_((sub_(d, as_elem(59))), (mod_((mul_(a, a)), m))));
	let temp_67_1 = (mul_((mod_((mul_(a, a)), m)), (sub_(d, as_elem(59)))));
	assert(eq_(temp_67_0, temp_67_1)) by {
		lemma_mul_comm(sub_(d, as_elem(59)), mod_(mul_(a, a), m));
	}
	let temp_68_0 = (mul_((mod_((mul_((mod_(a, m)), d)), m)), (mod_((mul_(d, (mod_(d, m)))), m))));
	let temp_68_1 = (mul_((mod_((mul_((mod_(a, m)), d)), m)), (mod_((mul_(d, (mod_((add_(d, (mul_((mul_((mul_(b, c)), (mul_(b, b)))), m)))), m)))), m))));
	assert(eq_(temp_68_0, temp_68_1)) by {
		cong_mul_(mod_(mul_(mod_(a, m), d), m), mod_(mul_(d, mod_(d, m)), m), mod_(mul_(mod_(a, m), d), m), mod_(mul_(d, mod_(add_(d, mul_(mul_(mul_(b, c), mul_(b, b)), m)), m)), m));
		lemma_mod_mul_vanish(d, mul_(mul_(b, c), mul_(b, b)), m);
		lemma_eq_ref(mod_(mul_(mod_(a, m), d), m));
		cong_mod_(mul_(d, mod_(d, m)), m, mul_(d, mod_(add_(d, mul_(mul_(mul_(b, c), mul_(b, b)), m)), m)), m);
		lemma_eq_ref(d);
		cong_mul_(d, mod_(d, m), d, mod_(add_(d, mul_(mul_(mul_(b, c), mul_(b, b)), m)), m));
		lemma_eq_ref(m);
	}
	let temp_69_0 = (mul_((mul_(c, a)), (mul_(d, d))));
	let temp_69_1 = (mul_(c, (mul_(a, (mul_(d, d))))));
	assert(eq_(temp_69_0, temp_69_1)) by {
		lemma_eq_sym(temp_69_1, temp_69_0);
		lemma_mul_assoc(c, a, mul_(d, d));
	}
	let temp_70_0 = (add_((mul_(a, d)), (mul_(b, a))));
	let temp_70_1 = (add_((mul_(a, d)), (mul_(a, b))));
	assert(eq_(temp_70_0, temp_70_1)) by {
		cong_add_(mul_(a, d), mul_(b, a), mul_(a, d), mul_(a, b));
		lemma_mul_comm(b, a);
		lemma_eq_ref(mul_(a, d));
	}
	let temp_71_0 = (add_(a, (mod_((mul_(b, b)), m))));
	let temp_71_1 = (add_(a, (mod_((mul_(b, b)), m))));
	assert(eq_(temp_71_0, temp_71_1)) by {
		lemma_eq_ref(temp_71_0);
	}
	let temp_72_0 = (mul_((mul_(b, b)), (mul_(d, as_elem(58)))));
	let temp_72_1 = (mul_((mul_(b, b)), (mul_(d, as_elem(58)))));
	assert(eq_(temp_72_0, temp_72_1)) by {
		lemma_eq_ref(temp_72_0);
	}
	let temp_73_0 = (mul_((mod_((add_((mod_(b, m)), b)), m)), (mul_(c, c))));
	let temp_73_1 = (mul_((mod_((add_((add_((mod_(b, m)), b)), (mul_((mul_((mul_(a, b)), (sub_(d, (mod_(d, m)))))), m)))), m)), (mul_(c, c))));
	assert(eq_(temp_73_0, temp_73_1)) by {
		lemma_mul_comm(c, c);
		lemma_mod_mul_vanish(add_(mod_(b, m), b), mul_(mul_(a, b), sub_(d, mod_(d, m))), m);
		cong_mul_(mod_(add_(mod_(b, m), b), m), mul_(c, c), mod_(add_(add_(mod_(b, m), b), mul_(mul_(mul_(a, b), sub_(d, mod_(d, m))), m)), m), mul_(c, c));
	}
	let temp_74_0 = (mul_((mul_(c, (mod_(b, m)))), (mul_(a, b))));
	let temp_74_1 = (mul_((mul_(c, (mod_((sub_(b, (mul_((mul_((mul_(b, b)), (sub_(b, a)))), m)))), m)))), (mul_(a, b))));
	assert(eq_(temp_74_0, temp_74_1)) by {
		lemma_mod_mul_vanish(b, mul_(mul_(b, b), sub_(b, a)), m);
		cong_mul_(mul_(c, mod_(b, m)), mul_(a, b), mul_(c, mod_(sub_(b, mul_(mul_(mul_(b, b), sub_(b, a)), m)), m)), mul_(a, b));
		lemma_eq_ref(c);
		cong_mul_(c, mod_(b, m), c, mod_(sub_(b, mul_(mul_(mul_(b, b), sub_(b, a)), m)), m));
		lemma_eq_ref(mul_(a, b));
	}
	let temp_75_0 = (mul_((mul_(d, a)), (mul_(b, c))));
	let temp_75_1 = (mul_(d, (mul_(a, (mul_(b, c))))));
	assert(eq_(temp_75_0, temp_75_1)) by {
		lemma_eq_sym(temp_75_1, temp_75_0);
		lemma_mul_assoc(d, a, mul_(b, c));
	}
	let temp_76_0 = (mul_((mul_(d, d)), (mul_(b, b))));
	let temp_76_1 = (mul_((mul_((mul_(d, d)), b)), b));
	assert(eq_(temp_76_0, temp_76_1)) by {
		lemma_mul_assoc(mul_(d, d), b, b);
	}
	let temp_77_0 = (mod_((mul_(a, (mul_(a, c)))), m));
	let temp_77_1 = (mod_((mul_(a, (mul_(c, a)))), m));
	assert(eq_(temp_77_0, temp_77_1)) by {
		cong_mod_(mul_(a, mul_(a, c)), m, mul_(a, mul_(c, a)), m);
		lemma_mul_comm(a, c);
		lemma_eq_ref(m);
		cong_mul_(a, mul_(a, c), a, mul_(c, a));
		lemma_eq_ref(a);
	}
	let temp_78_0 = (mul_((mul_(c, a)), (sub_(a, c))));
	let temp_78_1 = (mul_((sub_(a, c)), (mul_(c, a))));
	assert(eq_(temp_78_0, temp_78_1)) by {
		lemma_mul_comm(mul_(c, a), sub_(a, c));
	}
	let temp_79_0 = (mul_(d, (sub_(c, (mod_(a, m))))));
	let temp_79_1 = (mul_((sub_(c, (mod_(a, m)))), d));
	assert(eq_(temp_79_0, temp_79_1)) by {
		lemma_mul_comm(d, sub_(c, mod_(a, m)));
	}
	let temp_80_0 = (mul_((mul_(c, c)), (mul_(b, d))));
	let temp_80_1 = (mul_((mul_(b, d)), (mul_(c, c))));
	assert(eq_(temp_80_0, temp_80_1)) by {
		lemma_mul_comm(mul_(c, c), mul_(b, d));
	}
	let temp_81_0 = (mul_((mul_(c, c)), (mod_((mul_(a, c)), m))));
	let temp_81_1 = (mul_((mul_(c, c)), (mod_((add_((mul_((mul_((mod_((mul_(a, c)), m)), (mul_(c, a)))), m)), (mul_(a, c)))), m))));
	assert(eq_(temp_81_0, temp_81_1)) by {
		lemma_mul_comm(c, c);
		lemma_mod_mul_vanish(mul_(a, c), mul_(mod_(mul_(a, c), m), mul_(c, a)), m);
		cong_mul_(mul_(c, c), mod_(mul_(a, c), m), mul_(c, c), mod_(add_(mul_(mul_(mod_(mul_(a, c), m), mul_(c, a)), m), mul_(a, c)), m));
	}
	let temp_82_0 = (mul_((mod_((mul_(a, (mod_(as_elem(74), m)))), m)), (mul_(a, c))));
	let temp_82_1 = (mul_((mul_(a, c)), (mod_((mul_(a, (mod_(as_elem(74), m)))), m))));
	assert(eq_(temp_82_0, temp_82_1)) by {
		lemma_mul_comm(mod_(mul_(a, mod_(as_elem(74), m)), m), mul_(a, c));
	}
	let temp_83_0 = (sub_((mul_(c, c)), (mul_((mod_(c, m)), a))));
	let temp_83_1 = (sub_((mul_(c, c)), (mul_(a, (mod_(c, m))))));
	assert(eq_(temp_83_0, temp_83_1)) by {
		cong_sub_(mul_(c, c), mul_(mod_(c, m), a), mul_(c, c), mul_(a, mod_(c, m)));
		lemma_mul_comm(c, c);
		lemma_mul_comm(mod_(c, m), a);
	}
	let temp_84_0 = (mul_((mul_((mod_(a, m)), b)), (add_(b, b))));
	let temp_84_1 = (add_((mul_((mul_((mod_(a, m)), b)), b)), (mul_((mul_((mod_(a, m)), b)), b))));
	assert(eq_(temp_84_0, temp_84_1)) by {
		lemma_mul_dist(mul_(mod_(a, m), b), b, b);
	}
	let temp_85_0 = (mul_((mul_(c, d)), (mod_((mul_(b, d)), m))));
	let temp_85_1 = (mul_((mul_(c, d)), (mod_((mul_(d, b)), m))));
	assert(eq_(temp_85_0, temp_85_1)) by {
		lemma_mul_comm(b, d);
		cong_mul_(mul_(c, d), mod_(mul_(b, d), m), mul_(c, d), mod_(mul_(d, b), m));
		lemma_eq_ref(mul_(c, d));
		cong_mod_(mul_(b, d), m, mul_(d, b), m);
		lemma_eq_ref(m);
	}
	let temp_86_0 = (mul_((mul_(d, a)), (mul_(a, a))));
	let temp_86_1 = (mul_((mul_(a, d)), (mul_(a, a))));
	assert(eq_(temp_86_0, temp_86_1)) by {
		cong_mul_(mul_(d, a), mul_(a, a), mul_(a, d), mul_(a, a));
		lemma_mul_comm(d, a);
		lemma_mul_comm(a, a);
	}
	let temp_87_0 = (add_((sub_(a, c)), (mul_(d, a))));
	let temp_87_1 = (add_((sub_(a, c)), (mul_(a, d))));
	assert(eq_(temp_87_0, temp_87_1)) by {
		cong_add_(sub_(a, c), mul_(d, a), sub_(a, c), mul_(a, d));
		lemma_mul_comm(d, a);
		lemma_eq_ref(sub_(a, c));
	}
	let temp_88_0 = (sub_((mul_(b, b)), (add_(c, as_elem(2)))));
	let temp_88_1 = (sub_((mul_(b, b)), (add_(c, as_elem(2)))));
	assert(eq_(temp_88_0, temp_88_1)) by {
		lemma_eq_ref(temp_88_0);
	}
	let temp_89_0 = (mul_((mul_(d, b)), (mul_(b, b))));
	let temp_89_1 = (mul_(d, (mul_(b, (mul_(b, b))))));
	assert(eq_(temp_89_0, temp_89_1)) by {
		lemma_eq_sym(temp_89_1, temp_89_0);
		lemma_mul_assoc(d, b, mul_(b, b));
	}
	let temp_90_0 = (sub_((mul_((mod_(c, m)), d)), (mul_(d, d))));
	let temp_90_1 = (sub_((mul_((mod_((add_(c, (mul_((mod_((mul_((mul_(b, b)), (mul_(as_elem(56), b)))), m)), m)))), m)), d)), (mul_(d, d))));
	assert(eq_(temp_90_0, temp_90_1)) by {
		lemma_mul_comm(d, d);
		lemma_mod_mul_vanish(c, mod_(mul_(mul_(b, b), mul_(as_elem(56), b)), m), m);
		cong_sub_(mul_(mod_(c, m), d), mul_(d, d), mul_(mod_(add_(c, mul_(mod_(mul_(mul_(b, b), mul_(as_elem(56), b)), m), m)), m), d), mul_(d, d));
		lemma_eq_ref(d);
		cong_mul_(mod_(c, m), d, mod_(add_(c, mul_(mod_(mul_(mul_(b, b), mul_(as_elem(56), b)), m), m)), m), d);
	}
	let temp_91_0 = (mul_((mul_(a, a)), (mul_((mod_(d, m)), d))));
	let temp_91_1 = (mul_(a, (mul_(a, (mul_((mod_(d, m)), d))))));
	assert(eq_(temp_91_0, temp_91_1)) by {
		lemma_eq_sym(temp_91_1, temp_91_0);
		lemma_mul_assoc(a, a, mul_(mod_(d, m), d));
	}
	let temp_92_0 = (mul_((mul_(b, a)), (mul_(b, b))));
	let temp_92_1 = (mul_(b, (mul_(a, (mul_(b, b))))));
	assert(eq_(temp_92_0, temp_92_1)) by {
		lemma_eq_sym(temp_92_1, temp_92_0);
		lemma_mul_assoc(b, a, mul_(b, b));
	}
	let temp_93_0 = (mul_((mul_(c, a)), (mul_(d, (mod_(a, m))))));
	let temp_93_1 = (mul_((mul_(d, (mod_(a, m)))), (mul_(c, a))));
	assert(eq_(temp_93_0, temp_93_1)) by {
		lemma_mul_comm(mul_(c, a), mul_(d, mod_(a, m)));
	}
	let temp_94_0 = (mul_((mod_((mul_(a, as_elem(29))), m)), (mul_(c, (mod_(c, m))))));
	let temp_94_1 = (mul_((mod_((mul_(a, as_elem(29))), m)), (mul_((mod_(c, m)), c))));
	assert(eq_(temp_94_0, temp_94_1)) by {
		lemma_mul_comm(c, mod_(c, m));
		cong_mul_(mod_(mul_(a, as_elem(29)), m), mul_(c, mod_(c, m)), mod_(mul_(a, as_elem(29)), m), mul_(mod_(c, m), c));
		lemma_eq_ref(mod_(mul_(a, as_elem(29)), m));
	}
	let temp_95_0 = (sub_((mod_((add_(d, c)), m)), (mul_(a, b))));
	let temp_95_1 = (sub_((mod_((add_(d, c)), m)), (mul_(b, a))));
	assert(eq_(temp_95_0, temp_95_1)) by {
		lemma_mul_comm(a, b);
		cong_sub_(mod_(add_(d, c), m), mul_(a, b), mod_(add_(d, c), m), mul_(b, a));
		lemma_eq_ref(mod_(add_(d, c), m));
	}
	let temp_96_0 = (mul_((mul_(b, b)), (mul_(a, b))));
	let temp_96_1 = (mul_(b, (mul_(b, (mul_(a, b))))));
	assert(eq_(temp_96_0, temp_96_1)) by {
		lemma_eq_sym(temp_96_1, temp_96_0);
		lemma_mul_assoc(b, b, mul_(a, b));
	}
	let temp_97_0 = (sub_((mul_((mod_(c, m)), c)), (mul_((mod_(b, m)), a))));
	let temp_97_1 = (sub_((mul_((mod_(c, m)), c)), (mul_(a, (mod_(b, m))))));
	assert(eq_(temp_97_0, temp_97_1)) by {
		lemma_mul_comm(mod_(b, m), a);
		cong_sub_(mul_(mod_(c, m), c), mul_(mod_(b, m), a), mul_(mod_(c, m), c), mul_(a, mod_(b, m)));
		lemma_eq_ref(mul_(mod_(c, m), c));
	}
	let temp_98_0 = (sub_((mul_(b, c)), (mul_(b, c))));
	let temp_98_1 = (sub_((mul_(c, b)), (mul_(b, c))));
	assert(eq_(temp_98_0, temp_98_1)) by {
		cong_sub_(mul_(b, c), mul_(b, c), mul_(c, b), mul_(b, c));
		lemma_mul_comm(b, c);
		lemma_mul_comm(c, b);
		lemma_eq_trans(mul_(b, c), mul_(c, b), mul_(b, c));
	}
	let temp_99_0 = (mul_(b, (sub_(b, c))));
	let temp_99_1 = (mul_((sub_(b, c)), b));
	assert(eq_(temp_99_0, temp_99_1)) by {
		lemma_mul_comm(b, sub_(b, c));
	}
	let temp_100_0 = (mul_((add_(a, d)), (mul_(a, c))));
	let temp_100_1 = (mul_((add_(a, d)), (mul_(c, a))));
	assert(eq_(temp_100_0, temp_100_1)) by {
		cong_mul_(add_(a, d), mul_(a, c), add_(a, d), mul_(c, a));
		lemma_mul_comm(a, c);
		lemma_eq_ref(add_(a, d));
	}
	let temp_101_0 = (sub_((mul_(d, c)), (mul_(b, a))));
	let temp_101_1 = (sub_((mul_(c, d)), (mul_(b, a))));
	assert(eq_(temp_101_0, temp_101_1)) by {
		cong_sub_(mul_(d, c), mul_(b, a), mul_(c, d), mul_(b, a));
		lemma_mul_comm(d, c);
		lemma_eq_ref(mul_(b, a));
	}
	let temp_102_0 = (mul_((mod_((mul_(a, a)), m)), (sub_(a, b))));
	let temp_102_1 = (mul_((mod_((mul_(a, a)), m)), (sub_(a, b))));
	assert(eq_(temp_102_0, temp_102_1)) by {
		lemma_eq_ref(temp_102_0);
	}
	let temp_103_0 = (mul_((mul_(b, (mod_(b, m)))), (mul_(a, b))));
	let temp_103_1 = (mul_((mul_((mul_(b, (mod_(b, m)))), a)), b));
	assert(eq_(temp_103_0, temp_103_1)) by {
		lemma_mul_assoc(mul_(b, mod_(b, m)), a, b);
	}
	let temp_104_0 = (mul_((sub_(a, c)), a));
	let temp_104_1 = (mul_(a, (sub_(a, c))));
	assert(eq_(temp_104_0, temp_104_1)) by {
		lemma_mul_comm(sub_(a, c), a);
	}
	let temp_105_0 = (mod_((mul_((mul_(d, c)), c)), m));
	let temp_105_1 = (mod_((mul_((mul_(c, d)), c)), m));
	assert(eq_(temp_105_0, temp_105_1)) by {
		cong_mod_(mul_(mul_(d, c), c), m, mul_(mul_(c, d), c), m);
		lemma_mul_comm(d, c);
		lemma_eq_ref(m);
		cong_mul_(mul_(d, c), c, mul_(c, d), c);
		lemma_eq_ref(c);
	}
	let temp_106_0 = (mul_((mul_(a, d)), (mul_(d, b))));
	let temp_106_1 = (mul_((mul_((mul_(a, d)), d)), b));
	assert(eq_(temp_106_0, temp_106_1)) by {
		lemma_mul_assoc(mul_(a, d), d, b);
	}
	let temp_107_0 = (mul_((mod_((mul_(d, a)), m)), (mul_((mod_(b, m)), d))));
	let temp_107_1 = (mul_((mul_((mod_((mul_(d, a)), m)), (mod_(b, m)))), d));
	assert(eq_(temp_107_0, temp_107_1)) by {
		lemma_mul_assoc(mod_(mul_(d, a), m), mod_(b, m), d);
	}
	let temp_108_0 = (mul_((mul_((mod_(b, m)), b)), (mul_(b, d))));
	let temp_108_1 = (mul_((mod_(b, m)), (mul_(b, (mul_(b, d))))));
	assert(eq_(temp_108_0, temp_108_1)) by {
		lemma_eq_sym(temp_108_1, temp_108_0);
		lemma_mul_assoc(mod_(b, m), b, mul_(b, d));
	}
	let temp_109_0 = (mul_((mul_(c, d)), (mul_(d, (mod_(c, m))))));
	let temp_109_1 = (mul_((mul_(c, d)), (mul_(d, (mod_((sub_(c, (mul_((mul_((mul_(d, d)), (sub_(d, d)))), m)))), m))))));
	assert(eq_(temp_109_0, temp_109_1)) by {
		lemma_eq_ref(d);
		lemma_eq_ref(mul_(c, d));
		lemma_mod_mul_vanish(c, mul_(mul_(d, d), sub_(d, d)), m);
		cong_mul_(mul_(c, d), mul_(d, mod_(c, m)), mul_(c, d), mul_(d, mod_(sub_(c, mul_(mul_(mul_(d, d), sub_(d, d)), m)), m)));
		cong_mul_(d, mod_(c, m), d, mod_(sub_(c, mul_(mul_(mul_(d, d), sub_(d, d)), m)), m));
	}
	let temp_110_0 = (mul_((mul_(d, c)), (mul_(b, a))));
	let temp_110_1 = (mul_((mul_(b, a)), (mul_(d, c))));
	assert(eq_(temp_110_0, temp_110_1)) by {
		lemma_mul_comm(mul_(d, c), mul_(b, a));
	}
	let temp_111_0 = (mul_((mul_(d, d)), (add_(b, (mod_(c, m))))));
	let temp_111_1 = (mul_((mul_(d, d)), (add_(b, (mod_((sub_(c, (mul_((mul_((mul_(a, (mod_(a, m)))), (mul_(d, b)))), m)))), m))))));
	assert(eq_(temp_111_0, temp_111_1)) by {
		cong_add_(b, mod_(c, m), b, mod_(sub_(c, mul_(mul_(mul_(a, mod_(a, m)), mul_(d, b)), m)), m));
		lemma_mul_comm(d, d);
		lemma_mod_mul_vanish(c, mul_(mul_(a, mod_(a, m)), mul_(d, b)), m);
		cong_mul_(mul_(d, d), add_(b, mod_(c, m)), mul_(d, d), add_(b, mod_(sub_(c, mul_(mul_(mul_(a, mod_(a, m)), mul_(d, b)), m)), m)));
		lemma_eq_ref(b);
	}
	let temp_112_0 = (mul_((mul_((mod_(as_elem(75), m)), c)), (mul_(as_elem(45), d))));
	let temp_112_1 = (mul_((mul_((mod_(as_elem(75), m)), c)), (mul_(d, as_elem(45)))));
	assert(eq_(temp_112_0, temp_112_1)) by {
		lemma_mul_comm(as_elem(45), d);
		cong_mul_(mul_(mod_(as_elem(75), m), c), mul_(as_elem(45), d), mul_(mod_(as_elem(75), m), c), mul_(d, as_elem(45)));
		lemma_eq_ref(mul_(mod_(as_elem(75), m), c));
	}
	let temp_113_0 = (mul_((add_(a, b)), (mul_(d, c))));
	let temp_113_1 = (mul_((mul_((add_(a, b)), d)), c));
	assert(eq_(temp_113_0, temp_113_1)) by {
		lemma_mul_assoc(add_(a, b), d, c);
	}
	let temp_114_0 = (sub_((mul_(d, d)), (mul_(c, d))));
	let temp_114_1 = (mul_((sub_(d, c)), d));
	assert(eq_(temp_114_0, temp_114_1)) by {
		lemma_eq_sym(temp_114_1, temp_114_0);
		lemma_mul_dist(d, d, c);
	}
	let temp_115_0 = (mul_((mul_(a, a)), (mul_(c, b))));
	let temp_115_1 = (mul_(a, (mul_(a, (mul_(c, b))))));
	assert(eq_(temp_115_0, temp_115_1)) by {
		lemma_eq_sym(temp_115_1, temp_115_0);
		lemma_mul_assoc(a, a, mul_(c, b));
	}
	let temp_116_0 = (mul_((mod_((mul_(b, a)), m)), (mul_(b, c))));
	let temp_116_1 = (mul_((mul_((mod_((mul_(b, a)), m)), b)), c));
	assert(eq_(temp_116_0, temp_116_1)) by {
		lemma_mul_assoc(mod_(mul_(b, a), m), b, c);
	}
	let temp_117_0 = (mul_((mod_((mul_(d, c)), m)), (mul_(a, d))));
	let temp_117_1 = (mul_((mul_((mod_((mul_(d, c)), m)), a)), d));
	assert(eq_(temp_117_0, temp_117_1)) by {
		lemma_mul_assoc(mod_(mul_(d, c), m), a, d);
	}
	let temp_118_0 = (mul_((sub_(b, d)), (mul_(a, b))));
	let temp_118_1 = (sub_((mul_(b, (mul_(a, b)))), (mul_(d, (mul_(a, b))))));
	assert(eq_(temp_118_0, temp_118_1)) by {
		lemma_mul_dist(mul_(a, b), b, d);
	}
	let temp_119_0 = (mul_((sub_(c, d)), (mul_(a, (mod_(c, m))))));
	let temp_119_1 = (mul_((mul_((sub_(c, d)), a)), (mod_(c, m))));
	assert(eq_(temp_119_0, temp_119_1)) by {
		lemma_mul_assoc(sub_(c, d), a, mod_(c, m));
	}
	let temp_120_0 = (add_((mul_(c, c)), (mul_(a, b))));
	let temp_120_1 = (add_((mul_(a, b)), (mul_(c, c))));
	assert(eq_(temp_120_0, temp_120_1)) by {
		lemma_add_comm(mul_(c, c), mul_(a, b));
	}

}

} // verus!