use builtin_macros::*;
// use builtin::*;
mod nl_basics;
use crate::nl_basics::*;
verus! {

pub proof fn free_0(a: Elem, b: Elem, c: Elem, d: Elem, m: Elem)
{
	let temp_0_0 = (mul_((mul_(a, b)), (mul_(d, b))));
	let temp_0_1 = (mul_((mul_((mul_(a, b)), d)), b));
	assert(eq_(temp_0_0, temp_0_1)) by {
		lemma_mul_assoc(mul_(a, b), d, b);
	}
	let temp_1_0 = (mul_((mul_(d, b)), (add_(b, b))));
	let temp_1_1 = (mul_((add_(b, b)), (mul_(d, b))));
	assert(eq_(temp_1_0, temp_1_1)) by {
		lemma_mul_comm(mul_(d, b), add_(b, b));
	}
	let temp_2_0 = (mul_((mul_(b, d)), (mul_(d, (mod_(d, m))))));
	let temp_2_1 = (mul_(b, (mul_(d, (mul_(d, (mod_(d, m))))))));
	assert(eq_(temp_2_0, temp_2_1)) by {
		lemma_eq_sym(temp_2_1, temp_2_0);
		lemma_mul_assoc(b, d, mul_(d, mod_(d, m)));
	}
	let temp_3_0 = (mul_((add_(c, b)), (add_(b, a))));
	let temp_3_1 = (mul_((add_(b, a)), (add_(c, b))));
	assert(eq_(temp_3_0, temp_3_1)) by {
		lemma_mul_comm(add_(c, b), add_(b, a));
	}
	let temp_4_0 = (mul_((mod_((mul_(c, (mod_(d, m)))), m)), (mul_(b, a))));
	let temp_4_1 = (mul_((mod_((mod_((mul_(c, d)), m)), m)), (mul_(b, a))));
	assert(eq_(temp_4_0, temp_4_1)) by {
		lemma_mod_mul_noop(c, d, m);
		cong_mul_(mod_(mul_(c, mod_(d, m)), m), mul_(b, a), mod_(mod_(mul_(c, d), m), m), mul_(b, a));
		lemma_eq_ref(mul_(b, a));
		lemma_eq_sym(mod_(mod_(mul_(c, d), m), m), mod_(mul_(c, mod_(d, m)), m));
	}
	let temp_5_0 = (mul_((mul_(a, d)), (mod_((mul_(a, a)), m))));
	let temp_5_1 = (mul_((mul_(d, a)), (mod_((mul_(a, a)), m))));
	assert(eq_(temp_5_0, temp_5_1)) by {
		cong_mul_(mul_(a, d), mod_(mul_(a, a), m), mul_(d, a), mod_(mul_(a, a), m));
		lemma_mul_comm(a, d);
		lemma_eq_ref(mod_(mul_(a, a), m));
	}
	let temp_6_0 = (sub_((add_(d, a)), (mul_(d, d))));
	let temp_6_1 = (sub_((add_(a, d)), (mul_(d, d))));
	assert(eq_(temp_6_0, temp_6_1)) by {
		cong_sub_(add_(d, a), mul_(d, d), add_(a, d), mul_(d, d));
		lemma_add_comm(d, a);
		lemma_mul_comm(d, d);
	}
	let temp_7_0 = (mul_((mul_(d, b)), (mul_((mod_(c, m)), a))));
	let temp_7_1 = (mul_((mul_((mod_(c, m)), a)), (mul_(d, b))));
	assert(eq_(temp_7_0, temp_7_1)) by {
		lemma_mul_comm(mul_(d, b), mul_(mod_(c, m), a));
	}
	let temp_8_0 = (mul_((mod_((mul_(d, b)), m)), (mul_((mod_(b, m)), c))));
	let temp_8_1 = (mul_((mul_((mod_((mul_(d, b)), m)), (mod_(b, m)))), c));
	assert(eq_(temp_8_0, temp_8_1)) by {
		lemma_mul_assoc(mod_(mul_(d, b), m), mod_(b, m), c);
	}
	let temp_9_0 = (mul_((sub_(c, as_elem(97))), (mul_(d, as_elem(34)))));
	let temp_9_1 = (mul_((mul_((sub_(c, as_elem(97))), d)), as_elem(34)));
	assert(eq_(temp_9_0, temp_9_1)) by {
		lemma_mul_assoc(sub_(c, as_elem(97)), d, as_elem(34));
	}
	let temp_10_0 = (mod_((sub_((add_(d, a)), (mod_((mul_((mod_(as_elem(20), m)), c)), m)))), m));
	let temp_10_1 = (mod_((sub_((add_(a, d)), (mod_((mul_((mod_(as_elem(20), m)), c)), m)))), m));
	assert(eq_(temp_10_0, temp_10_1)) by {
		lemma_add_comm(d, a);
		cong_mod_(sub_(add_(d, a), mod_(mul_(mod_(as_elem(20), m), c), m)), m, sub_(add_(a, d), mod_(mul_(mod_(as_elem(20), m), c), m)), m);
		lemma_eq_ref(m);
		cong_sub_(add_(d, a), mod_(mul_(mod_(as_elem(20), m), c), m), add_(a, d), mod_(mul_(mod_(as_elem(20), m), c), m));
		lemma_eq_ref(mod_(mul_(mod_(as_elem(20), m), c), m));
	}
	let temp_11_0 = (mul_((mod_((mul_(a, b)), m)), (mul_(b, d))));
	let temp_11_1 = (mul_((mod_((mul_(a, b)), m)), (mul_(d, b))));
	assert(eq_(temp_11_0, temp_11_1)) by {
		lemma_mul_comm(b, d);
		cong_mul_(mod_(mul_(a, b), m), mul_(b, d), mod_(mul_(a, b), m), mul_(d, b));
		lemma_eq_ref(mod_(mul_(a, b), m));
	}
	let temp_12_0 = (mod_((add_((mul_(b, a)), (mul_(a, d)))), m));
	let temp_12_1 = (mod_((add_((mul_(a, d)), (mul_(b, a)))), m));
	assert(eq_(temp_12_0, temp_12_1)) by {
		lemma_add_comm(mul_(b, a), mul_(a, d));
		cong_mod_(add_(mul_(b, a), mul_(a, d)), m, add_(mul_(a, d), mul_(b, a)), m);
		lemma_eq_ref(m);
	}
	let temp_13_0 = (mul_((mul_(c, a)), (mul_(c, c))));
	let temp_13_1 = (mul_((mul_(c, c)), (mul_(c, a))));
	assert(eq_(temp_13_0, temp_13_1)) by {
		lemma_mul_comm(mul_(c, a), mul_(c, c));
	}
	let temp_14_0 = (sub_((mul_(c, b)), (mul_(b, a))));
	let temp_14_1 = (sub_((mul_(c, b)), (mul_(a, b))));
	assert(eq_(temp_14_0, temp_14_1)) by {
		cong_sub_(mul_(c, b), mul_(b, a), mul_(c, b), mul_(a, b));
		lemma_mul_comm(b, a);
		lemma_eq_ref(mul_(c, b));
	}
	let temp_15_0 = (mul_((mul_(b, c)), (mul_(c, b))));
	let temp_15_1 = (mul_(b, (mul_(c, (mul_(c, b))))));
	assert(eq_(temp_15_0, temp_15_1)) by {
		lemma_eq_sym(temp_15_1, temp_15_0);
		lemma_mul_assoc(b, c, mul_(c, b));
	}
	let temp_16_0 = (mul_((mul_(c, b)), (mul_((mod_(b, m)), d))));
	let temp_16_1 = (mul_((mul_((mul_(c, b)), (mod_(b, m)))), d));
	assert(eq_(temp_16_0, temp_16_1)) by {
		lemma_mul_assoc(mul_(c, b), mod_(b, m), d);
	}
	let temp_17_0 = (mul_((mul_(c, d)), (add_(b, a))));
	let temp_17_1 = (mul_((mul_(c, d)), (add_(a, b))));
	assert(eq_(temp_17_0, temp_17_1)) by {
		lemma_add_comm(b, a);
		cong_mul_(mul_(c, d), add_(b, a), mul_(c, d), add_(a, b));
		lemma_eq_ref(mul_(c, d));
	}
	let temp_18_0 = (mul_((mul_(b, a)), (mod_((sub_(b, a)), m))));
	let temp_18_1 = (mul_((mul_(b, a)), (mod_((sub_(b, (mod_(a, m)))), m))));
	assert(eq_(temp_18_0, temp_18_1)) by {
		lemma_eq_ref(mul_(b, a));
		cong_mul_(mul_(b, a), mod_(sub_(b, a), m), mul_(b, a), mod_(sub_(b, mod_(a, m)), m));
		lemma_mod_sub_noop(b, a, m);
	}
	let temp_19_0 = (mod_((mul_((sub_(a, b)), (add_(d, b)))), m));
	let temp_19_1 = (mod_((sub_((mul_((sub_(a, b)), (add_(d, b)))), (mul_((mul_((mul_(b, (mod_(b, m)))), (mul_(c, c)))), m)))), m));
	assert(eq_(temp_19_0, temp_19_1)) by {
		lemma_mod_mul_vanish(mul_(sub_(a, b), add_(d, b)), mul_(mul_(b, mod_(b, m)), mul_(c, c)), m);
	}
	let temp_20_0 = (mul_((mul_(c, b)), (mul_(a, c))));
	let temp_20_1 = (mul_((mul_(a, c)), (mul_(c, b))));
	assert(eq_(temp_20_0, temp_20_1)) by {
		lemma_mul_comm(mul_(c, b), mul_(a, c));
	}
	let temp_21_0 = (mul_((sub_(d, a)), (mul_(b, d))));
	let temp_21_1 = (mul_((mul_((sub_(d, a)), b)), d));
	assert(eq_(temp_21_0, temp_21_1)) by {
		lemma_mul_assoc(sub_(d, a), b, d);
	}
	let temp_22_0 = (mul_((mul_(d, c)), (mul_(d, b))));
	let temp_22_1 = (mul_((mul_((mul_(d, c)), d)), b));
	assert(eq_(temp_22_0, temp_22_1)) by {
		lemma_mul_assoc(mul_(d, c), d, b);
	}
	let temp_23_0 = (mul_((mul_(a, a)), b));
	let temp_23_1 = (mul_(b, (mul_(a, a))));
	assert(eq_(temp_23_0, temp_23_1)) by {
		lemma_mul_comm(mul_(a, a), b);
	}
	let temp_24_0 = (add_((mul_(d, (mod_(c, m)))), (mul_(b, b))));
	let temp_24_1 = (add_((mul_(b, b)), (mul_(d, (mod_(c, m))))));
	assert(eq_(temp_24_0, temp_24_1)) by {
		lemma_add_comm(mul_(d, mod_(c, m)), mul_(b, b));
	}
	let temp_25_0 = (mod_((mul_((mul_(d, a)), (add_((mod_(a, m)), d)))), m));
	let temp_25_1 = (mod_((mul_((add_((mod_(a, m)), d)), (mul_(d, a)))), m));
	assert(eq_(temp_25_0, temp_25_1)) by {
		lemma_mul_comm(mul_(d, a), add_(mod_(a, m), d));
		cong_mod_(mul_(mul_(d, a), add_(mod_(a, m), d)), m, mul_(add_(mod_(a, m), d), mul_(d, a)), m);
		lemma_eq_ref(m);
	}
	let temp_26_0 = (mul_((mod_((mul_(a, b)), m)), (mul_((mod_(b, m)), d))));
	let temp_26_1 = (mul_((mul_((mod_((mul_(a, b)), m)), (mod_(b, m)))), d));
	assert(eq_(temp_26_0, temp_26_1)) by {
		lemma_mul_assoc(mod_(mul_(a, b), m), mod_(b, m), d);
	}
	let temp_27_0 = (mul_((mul_(d, a)), (add_(c, b))));
	let temp_27_1 = (mul_((add_(c, b)), (mul_(d, a))));
	assert(eq_(temp_27_0, temp_27_1)) by {
		lemma_mul_comm(mul_(d, a), add_(c, b));
	}
	let temp_28_0 = (add_((mul_((mod_(a, m)), d)), (mul_(c, a))));
	let temp_28_1 = (add_((mul_((mod_(a, m)), d)), (mul_(a, c))));
	assert(eq_(temp_28_0, temp_28_1)) by {
		lemma_mul_comm(c, a);
		cong_add_(mul_(mod_(a, m), d), mul_(c, a), mul_(mod_(a, m), d), mul_(a, c));
		lemma_eq_ref(mul_(mod_(a, m), d));
	}
	let temp_29_0 = (sub_((sub_(b, (mod_(c, m)))), (mul_(b, a))));
	let temp_29_1 = (sub_((sub_(b, (mod_(c, m)))), (mul_(a, b))));
	assert(eq_(temp_29_0, temp_29_1)) by {
		lemma_mul_comm(b, a);
		cong_sub_(sub_(b, mod_(c, m)), mul_(b, a), sub_(b, mod_(c, m)), mul_(a, b));
		lemma_eq_ref(sub_(b, mod_(c, m)));
	}
	let temp_30_0 = (mul_((mul_(a, b)), (mul_(a, (mod_(b, m))))));
	let temp_30_1 = (mul_((mul_(a, (mod_(b, m)))), (mul_(a, b))));
	assert(eq_(temp_30_0, temp_30_1)) by {
		lemma_mul_comm(mul_(a, b), mul_(a, mod_(b, m)));
	}
	let temp_31_0 = (add_((mul_(b, b)), (mul_(b, d))));
	let temp_31_1 = (mul_(b, (add_(b, d))));
	assert(eq_(temp_31_0, temp_31_1)) by {
		lemma_eq_sym(temp_31_1, temp_31_0);
		lemma_mul_dist(b, b, d);
	}
	let temp_32_0 = (mod_((mul_((sub_(a, c)), (add_(a, a)))), m));
	let temp_32_1 = (mod_((add_((mul_((sub_((mul_((mod_(a, m)), b)), (mod_((mul_(as_elem(48), c)), m)))), m)), (mul_((sub_(a, c)), (add_(a, a)))))), m));
	assert(eq_(temp_32_0, temp_32_1)) by {
		lemma_mod_mul_vanish(mul_(sub_(a, c), add_(a, a)), sub_(mul_(mod_(a, m), b), mod_(mul_(as_elem(48), c), m)), m);
	}
	let temp_33_0 = (mul_((mul_(b, c)), (mul_(a, a))));
	let temp_33_1 = (mul_((mul_((mul_(b, c)), a)), a));
	assert(eq_(temp_33_0, temp_33_1)) by {
		lemma_mul_assoc(mul_(b, c), a, a);
	}
	let temp_34_0 = (add_((mul_(c, c)), (mul_(b, c))));
	let temp_34_1 = (add_((mul_(b, c)), (mul_(c, c))));
	assert(eq_(temp_34_0, temp_34_1)) by {
		lemma_add_comm(mul_(c, c), mul_(b, c));
	}
	let temp_35_0 = (mul_((mul_(a, c)), (mul_(b, c))));
	let temp_35_1 = (mul_((mul_(a, c)), (mul_(c, b))));
	assert(eq_(temp_35_0, temp_35_1)) by {
		cong_mul_(mul_(a, c), mul_(b, c), mul_(a, c), mul_(c, b));
		lemma_mul_comm(b, c);
		lemma_eq_ref(mul_(a, c));
	}
	let temp_36_0 = (mul_((mul_(d, c)), (sub_(a, a))));
	let temp_36_1 = (mul_((mul_(c, d)), (sub_(a, a))));
	assert(eq_(temp_36_0, temp_36_1)) by {
		lemma_eq_ref(sub_(a, a));
		cong_mul_(mul_(d, c), sub_(a, a), mul_(c, d), sub_(a, a));
		lemma_mul_comm(d, c);
	}
	let temp_37_0 = (mul_((sub_(a, a)), (mul_(c, d))));
	let temp_37_1 = (sub_((mul_(a, (mul_(c, d)))), (mul_(a, (mul_(c, d))))));
	assert(eq_(temp_37_0, temp_37_1)) by {
		lemma_mul_dist(mul_(c, d), a, a);
	}
	let temp_38_0 = (sub_((mul_(a, a)), (mul_(d, d))));
	let temp_38_1 = (sub_((mul_(a, a)), (mul_(d, d))));
	assert(eq_(temp_38_0, temp_38_1)) by {
		lemma_eq_ref(temp_38_0);
	}
	let temp_39_0 = (mod_((mul_(a, (mul_(b, d)))), m));
	let temp_39_1 = (mod_((add_((mul_(a, (mul_(b, d)))), (mul_((mod_((mul_((mod_((mul_(d, (mod_(c, m)))), m)), (mul_((mod_(b, m)), b)))), m)), m)))), m));
	assert(eq_(temp_39_0, temp_39_1)) by {
		lemma_mod_mul_vanish(mul_(a, mul_(b, d)), mod_(mul_(mod_(mul_(d, mod_(c, m)), m), mul_(mod_(b, m), b)), m), m);
	}
	let temp_40_0 = (mul_((sub_(b, d)), (add_(c, d))));
	let temp_40_1 = (sub_((mul_(b, (add_(c, d)))), (mul_(d, (add_(c, d))))));
	assert(eq_(temp_40_0, temp_40_1)) by {
		lemma_mul_dist(add_(c, d), b, d);
	}
	let temp_41_0 = (add_((mod_((mul_(b, c)), m)), (mul_(d, b))));
	let temp_41_1 = (add_((mod_((mul_(b, c)), m)), (mul_(b, d))));
	assert(eq_(temp_41_0, temp_41_1)) by {
		lemma_mul_comm(d, b);
		cong_add_(mod_(mul_(b, c), m), mul_(d, b), mod_(mul_(b, c), m), mul_(b, d));
		lemma_eq_ref(mod_(mul_(b, c), m));
	}
	let temp_42_0 = (mul_((mul_(a, d)), (mod_((add_(a, (mod_(d, m)))), m))));
	let temp_42_1 = (mul_((mul_(a, d)), (mod_((add_((mod_(d, m)), a)), m))));
	assert(eq_(temp_42_0, temp_42_1)) by {
		lemma_add_comm(a, mod_(d, m));
		cong_mul_(mul_(a, d), mod_(add_(a, mod_(d, m)), m), mul_(a, d), mod_(add_(mod_(d, m), a), m));
		lemma_eq_ref(mul_(a, d));
		cong_mod_(add_(a, mod_(d, m)), m, add_(mod_(d, m), a), m);
		lemma_eq_ref(m);
	}
	let temp_43_0 = (mul_((mul_(c, (mod_(d, m)))), (mul_(b, b))));
	let temp_43_1 = (mul_((mul_((mul_(c, (mod_(d, m)))), b)), b));
	assert(eq_(temp_43_0, temp_43_1)) by {
		lemma_mul_assoc(mul_(c, mod_(d, m)), b, b);
	}
	let temp_44_0 = (mul_((mul_(a, d)), (mul_(d, b))));
	let temp_44_1 = (mul_(a, (mul_(d, (mul_(d, b))))));
	assert(eq_(temp_44_0, temp_44_1)) by {
		lemma_eq_sym(temp_44_1, temp_44_0);
		lemma_mul_assoc(a, d, mul_(d, b));
	}
	let temp_45_0 = (mul_((mul_(c, b)), (sub_(d, as_elem(21)))));
	let temp_45_1 = (mul_(c, (mul_(b, (sub_(d, as_elem(21)))))));
	assert(eq_(temp_45_0, temp_45_1)) by {
		lemma_mul_assoc(c, b, sub_(d, as_elem(21)));
		lemma_eq_sym(temp_45_1, temp_45_0);
	}
	let temp_46_0 = (mul_((mod_((mul_(b, b)), m)), (mul_(a, b))));
	let temp_46_1 = (mul_((mul_((mod_((mul_(b, b)), m)), a)), b));
	assert(eq_(temp_46_0, temp_46_1)) by {
		lemma_mul_assoc(mod_(mul_(b, b), m), a, b);
	}
	let temp_47_0 = (mul_((add_((mod_(b, m)), b)), (mul_(d, a))));
	let temp_47_1 = (mul_((mul_((add_((mod_(b, m)), b)), d)), a));
	assert(eq_(temp_47_0, temp_47_1)) by {
		lemma_mul_assoc(add_(mod_(b, m), b), d, a);
	}
	let temp_48_0 = (add_((mul_(c, (mod_(b, m)))), (mul_(a, a))));
	let temp_48_1 = (add_((mul_(c, (mod_(b, m)))), (mul_(a, a))));
	assert(eq_(temp_48_0, temp_48_1)) by {
		lemma_eq_ref(temp_48_0);
	}
	let temp_49_0 = (mul_((mul_(b, d)), (mul_(c, c))));
	let temp_49_1 = (mul_((mul_(b, d)), (mul_(c, c))));
	assert(eq_(temp_49_0, temp_49_1)) by {
		lemma_eq_ref(temp_49_0);
	}
	let temp_50_0 = (mul_((mul_(c, d)), (mod_((mul_((mod_(c, m)), a)), m))));
	let temp_50_1 = (mul_((mul_(c, d)), (mod_((add_((mul_((mul_((mul_((mod_(d, m)), d)), (sub_(a, a)))), m)), (mul_((mod_(c, m)), a)))), m))));
	assert(eq_(temp_50_0, temp_50_1)) by {
		lemma_mod_mul_vanish(mul_(mod_(c, m), a), mul_(mul_(mod_(d, m), d), sub_(a, a)), m);
		cong_mul_(mul_(c, d), mod_(mul_(mod_(c, m), a), m), mul_(c, d), mod_(add_(mul_(mul_(mul_(mod_(d, m), d), sub_(a, a)), m), mul_(mod_(c, m), a)), m));
		lemma_eq_ref(mul_(c, d));
	}
	let temp_51_0 = (mul_((add_(a, as_elem(85))), (mod_((mul_(d, b)), m))));
	let temp_51_1 = (mul_((add_(a, as_elem(85))), (mod_((add_((mul_((mul_((mul_(b, c)), (mul_(d, a)))), m)), (mul_(d, b)))), m))));
	assert(eq_(temp_51_0, temp_51_1)) by {
		lemma_mod_mul_vanish(mul_(d, b), mul_(mul_(b, c), mul_(d, a)), m);
		cong_mul_(add_(a, as_elem(85)), mod_(mul_(d, b), m), add_(a, as_elem(85)), mod_(add_(mul_(mul_(mul_(b, c), mul_(d, a)), m), mul_(d, b)), m));
		lemma_eq_ref(add_(a, as_elem(85)));
	}
	let temp_52_0 = (add_((sub_(c, c)), (mul_(c, (mod_(b, m))))));
	let temp_52_1 = (add_((mul_(c, (mod_(b, m)))), (sub_(c, c))));
	assert(eq_(temp_52_0, temp_52_1)) by {
		lemma_add_comm(sub_(c, c), mul_(c, mod_(b, m)));
	}
	let temp_53_0 = (mul_((add_(b, (mod_(b, m)))), (mul_(d, c))));
	let temp_53_1 = (add_((mul_(b, (mul_(d, c)))), (mul_((mod_(b, m)), (mul_(d, c))))));
	assert(eq_(temp_53_0, temp_53_1)) by {
		lemma_mul_dist(b, mod_(b, m), mul_(d, c));
	}
	let temp_54_0 = (mul_((mul_(c, a)), (mul_(d, c))));
	let temp_54_1 = (mul_((mul_((mul_(c, a)), d)), c));
	assert(eq_(temp_54_0, temp_54_1)) by {
		lemma_mul_assoc(mul_(c, a), d, c);
	}
	let temp_55_0 = (mul_((mod_((mul_(b, as_elem(84))), m)), (mod_((add_(b, c)), m))));
	let temp_55_1 = (mul_((mod_((sub_((mul_(b, as_elem(84))), (mul_((mul_((sub_(c, b)), d)), m)))), m)), (mod_((add_(b, c)), m))));
	assert(eq_(temp_55_0, temp_55_1)) by {
		lemma_mod_mul_vanish(mul_(b, as_elem(84)), mul_(sub_(c, b), d), m);
		cong_mul_(mod_(mul_(b, as_elem(84)), m), mod_(add_(b, c), m), mod_(sub_(mul_(b, as_elem(84)), mul_(mul_(sub_(c, b), d), m)), m), mod_(add_(b, c), m));
		lemma_eq_ref(mod_(add_(b, c), m));
	}
	let temp_56_0 = (mul_((mul_(a, c)), (mul_(d, d))));
	let temp_56_1 = (mul_(a, (mul_(c, (mul_(d, d))))));
	assert(eq_(temp_56_0, temp_56_1)) by {
		lemma_eq_sym(temp_56_1, temp_56_0);
		lemma_mul_assoc(a, c, mul_(d, d));
	}
	let temp_57_0 = (mul_((mul_(c, b)), (mul_(a, d))));
	let temp_57_1 = (mul_(c, (mul_(b, (mul_(a, d))))));
	assert(eq_(temp_57_0, temp_57_1)) by {
		lemma_eq_sym(temp_57_1, temp_57_0);
		lemma_mul_assoc(c, b, mul_(a, d));
	}
	let temp_58_0 = (mul_((mul_(b, a)), (mul_(d, c))));
	let temp_58_1 = (mul_(b, (mul_(a, (mul_(d, c))))));
	assert(eq_(temp_58_0, temp_58_1)) by {
		lemma_eq_sym(temp_58_1, temp_58_0);
		lemma_mul_assoc(b, a, mul_(d, c));
	}
	let temp_59_0 = (mul_((mul_(c, a)), (mul_(d, d))));
	let temp_59_1 = (mul_((mul_(a, c)), (mul_(d, d))));
	assert(eq_(temp_59_0, temp_59_1)) by {
		cong_mul_(mul_(c, a), mul_(d, d), mul_(a, c), mul_(d, d));
		lemma_mul_comm(c, a);
		lemma_mul_comm(d, d);
	}
	let temp_60_0 = (mul_((mul_((mod_(c, m)), d)), (mul_(b, d))));
	let temp_60_1 = (mul_((mul_(b, d)), (mul_((mod_(c, m)), d))));
	assert(eq_(temp_60_0, temp_60_1)) by {
		lemma_mul_comm(mul_(mod_(c, m), d), mul_(b, d));
	}
	let temp_61_0 = (mul_((mul_(a, c)), (mul_(c, a))));
	let temp_61_1 = (mul_((mul_(a, c)), (mul_(a, c))));
	assert(eq_(temp_61_0, temp_61_1)) by {
		cong_mul_(mul_(a, c), mul_(c, a), mul_(a, c), mul_(a, c));
		lemma_mul_comm(c, a);
		lemma_eq_ref(mul_(a, c));
	}
	let temp_62_0 = (add_((mul_(c, d)), (mod_((mul_(b, d)), m))));
	let temp_62_1 = (add_((mul_(c, d)), (mod_((mul_(d, b)), m))));
	assert(eq_(temp_62_0, temp_62_1)) by {
		lemma_mul_comm(b, d);
		cong_add_(mul_(c, d), mod_(mul_(b, d), m), mul_(c, d), mod_(mul_(d, b), m));
		lemma_eq_ref(m);
		lemma_eq_ref(mul_(c, d));
		cong_mod_(mul_(b, d), m, mul_(d, b), m);
	}
	let temp_63_0 = (sub_((mod_((add_(b, c)), m)), a));
	let temp_63_1 = (sub_((mod_((add_((mul_((mul_((add_(d, b)), (add_(c, b)))), m)), (add_(b, c)))), m)), a));
	assert(eq_(temp_63_0, temp_63_1)) by {
		lemma_mod_mul_vanish(add_(b, c), mul_(add_(d, b), add_(c, b)), m);
		cong_sub_(mod_(add_(b, c), m), a, mod_(add_(mul_(mul_(add_(d, b), add_(c, b)), m), add_(b, c)), m), a);
		lemma_eq_ref(a);
	}
	let temp_64_0 = (mul_((mul_(d, c)), (add_(c, c))));
	let temp_64_1 = (add_((mul_((mul_(d, c)), c)), (mul_((mul_(d, c)), c))));
	assert(eq_(temp_64_0, temp_64_1)) by {
		lemma_mul_dist(mul_(d, c), c, c);
	}
	let temp_65_0 = (mul_((mul_(c, (mod_(a, m)))), (mul_(a, b))));
	let temp_65_1 = (mul_((mul_((mul_(c, (mod_(a, m)))), a)), b));
	assert(eq_(temp_65_0, temp_65_1)) by {
		lemma_mul_assoc(mul_(c, mod_(a, m)), a, b);
	}
	let temp_66_0 = (mod_((add_((mul_(a, c)), (add_(c, d)))), m));
	let temp_66_1 = (mod_((add_((mul_(a, c)), (mod_((add_(c, d)), m)))), m));
	assert(eq_(temp_66_0, temp_66_1)) by {
		lemma_mod_add_noop(mul_(a, c), add_(c, d), m);
	}
	let temp_67_0 = (mul_((mod_((mul_(as_elem(20), d)), m)), (mul_(c, b))));
	let temp_67_1 = (mul_((mul_((mod_((mul_(as_elem(20), d)), m)), c)), b));
	assert(eq_(temp_67_0, temp_67_1)) by {
		lemma_mul_assoc(mod_(mul_(as_elem(20), d), m), c, b);
	}
	let temp_68_0 = (mul_((mul_(c, (mod_(d, m)))), (add_((mod_(a, m)), b))));
	let temp_68_1 = (mul_(c, (mul_((mod_(d, m)), (add_((mod_(a, m)), b))))));
	assert(eq_(temp_68_0, temp_68_1)) by {
		lemma_mul_assoc(c, mod_(d, m), add_(mod_(a, m), b));
		lemma_eq_sym(temp_68_1, temp_68_0);
	}
	let temp_69_0 = (sub_((mul_(c, d)), (mul_(c, b))));
	let temp_69_1 = (sub_((mul_(c, d)), (mul_(b, c))));
	assert(eq_(temp_69_0, temp_69_1)) by {
		cong_sub_(mul_(c, d), mul_(c, b), mul_(c, d), mul_(b, c));
		lemma_mul_comm(c, b);
		lemma_eq_ref(mul_(c, d));
	}
	let temp_70_0 = (sub_((sub_(a, d)), (mul_((mod_(d, m)), a))));
	let temp_70_1 = (sub_((sub_(a, d)), (mul_((mod_((add_((mul_((mul_((mul_(c, d)), (mul_(d, b)))), m)), d)), m)), a))));
	assert(eq_(temp_70_0, temp_70_1)) by {
		lemma_eq_ref(a);
		cong_mul_(mod_(d, m), a, mod_(add_(mul_(mul_(mul_(c, d), mul_(d, b)), m), d), m), a);
		lemma_eq_ref(sub_(a, d));
		lemma_mod_mul_vanish(d, mul_(mul_(c, d), mul_(d, b)), m);
		cong_sub_(sub_(a, d), mul_(mod_(d, m), a), sub_(a, d), mul_(mod_(add_(mul_(mul_(mul_(c, d), mul_(d, b)), m), d), m), a));
	}
	let temp_71_0 = (mul_((mul_(a, c)), (mul_(as_elem(97), c))));
	let temp_71_1 = (mul_((mul_((mul_(a, c)), as_elem(97))), c));
	assert(eq_(temp_71_0, temp_71_1)) by {
		lemma_mul_assoc(mul_(a, c), as_elem(97), c);
	}
	let temp_72_0 = (mul_((add_(c, c)), (mul_(d, a))));
	let temp_72_1 = (mul_((mul_(d, a)), (add_(c, c))));
	assert(eq_(temp_72_0, temp_72_1)) by {
		lemma_mul_comm(add_(c, c), mul_(d, a));
	}
	let temp_73_0 = (mul_((mul_((mod_(d, m)), b)), (mul_(c, b))));
	let temp_73_1 = (mul_((mod_(d, m)), (mul_(b, (mul_(c, b))))));
	assert(eq_(temp_73_0, temp_73_1)) by {
		lemma_mul_assoc(mod_(d, m), b, mul_(c, b));
		lemma_eq_sym(temp_73_1, temp_73_0);
	}
	let temp_74_0 = (mul_((mod_((add_((mod_(c, m)), b)), m)), (mul_(c, (mod_(c, m))))));
	let temp_74_1 = (mul_((mod_((sub_((add_((mod_(c, m)), b)), (mul_((mod_((mul_((mul_(a, a)), (sub_(d, d)))), m)), m)))), m)), (mul_(c, (mod_(c, m))))));
	assert(eq_(temp_74_0, temp_74_1)) by {
		lemma_mod_mul_vanish(add_(mod_(c, m), b), mod_(mul_(mul_(a, a), sub_(d, d)), m), m);
		cong_mul_(mod_(add_(mod_(c, m), b), m), mul_(c, mod_(c, m)), mod_(sub_(add_(mod_(c, m), b), mul_(mod_(mul_(mul_(a, a), sub_(d, d)), m), m)), m), mul_(c, mod_(c, m)));
		lemma_eq_ref(mul_(c, mod_(c, m)));
	}
	let temp_75_0 = (sub_((add_(b, b)), (mul_(a, as_elem(43)))));
	let temp_75_1 = (sub_((add_(b, b)), (mul_(a, as_elem(43)))));
	assert(eq_(temp_75_0, temp_75_1)) by {
		lemma_eq_ref(temp_75_0);
	}
	let temp_76_0 = (sub_((mul_(b, a)), (sub_(d, d))));
	let temp_76_1 = (sub_((mul_(a, b)), (sub_(d, d))));
	assert(eq_(temp_76_0, temp_76_1)) by {
		cong_sub_(mul_(b, a), sub_(d, d), mul_(a, b), sub_(d, d));
		lemma_mul_comm(b, a);
		lemma_eq_ref(sub_(d, d));
	}
	let temp_77_0 = (mul_((mul_(d, d)), (add_((mod_(a, m)), c))));
	let temp_77_1 = (mul_((mul_(d, d)), (add_((mod_(a, m)), c))));
	assert(eq_(temp_77_0, temp_77_1)) by {
		lemma_eq_ref(temp_77_0);
	}
	let temp_78_0 = (mul_((mul_((mod_(b, m)), (mod_(d, m)))), c));
	let temp_78_1 = (mul_(c, (mul_((mod_(b, m)), (mod_(d, m))))));
	assert(eq_(temp_78_0, temp_78_1)) by {
		lemma_mul_comm(mul_(mod_(b, m), mod_(d, m)), c);
	}
	let temp_79_0 = (mod_((mul_((sub_(d, (mod_(d, m)))), (mul_(d, c)))), m));
	let temp_79_1 = (mod_((mul_((sub_(d, (mod_((sub_(d, (mul_((mul_((mul_(b, (mod_(b, m)))), (add_(d, a)))), m)))), m)))), (mul_(d, c)))), m));
	assert(eq_(temp_79_0, temp_79_1)) by {
		lemma_mod_mul_vanish(d, mul_(mul_(b, mod_(b, m)), add_(d, a)), m);
		cong_mod_(mul_(sub_(d, mod_(d, m)), mul_(d, c)), m, mul_(sub_(d, mod_(sub_(d, mul_(mul_(mul_(b, mod_(b, m)), add_(d, a)), m)), m)), mul_(d, c)), m);
		lemma_eq_ref(d);
		lemma_eq_ref(mul_(d, c));
		cong_sub_(d, mod_(d, m), d, mod_(sub_(d, mul_(mul_(mul_(b, mod_(b, m)), add_(d, a)), m)), m));
		lemma_eq_ref(m);
		cong_mul_(sub_(d, mod_(d, m)), mul_(d, c), sub_(d, mod_(sub_(d, mul_(mul_(mul_(b, mod_(b, m)), add_(d, a)), m)), m)), mul_(d, c));
	}
	let temp_80_0 = (mod_((add_((mul_(a, c)), (mul_(d, c)))), m));
	let temp_80_1 = (mod_((sub_((add_((mul_(a, c)), (mul_(d, c)))), (mul_((mul_((mul_(b, d)), (mod_((mul_(d, a)), m)))), m)))), m));
	assert(eq_(temp_80_0, temp_80_1)) by {
		lemma_mod_mul_vanish(add_(mul_(a, c), mul_(d, c)), mul_(mul_(b, d), mod_(mul_(d, a), m)), m);
	}
	let temp_81_0 = (mul_((mul_((mod_(d, m)), b)), (mul_(d, c))));
	let temp_81_1 = (mul_((mul_((mod_((add_(d, (mul_((mul_((add_(c, c)), (sub_(a, a)))), m)))), m)), b)), (mul_(d, c))));
	assert(eq_(temp_81_0, temp_81_1)) by {
		lemma_mod_mul_vanish(d, mul_(add_(c, c), sub_(a, a)), m);
		cong_mul_(mul_(mod_(d, m), b), mul_(d, c), mul_(mod_(add_(d, mul_(mul_(add_(c, c), sub_(a, a)), m)), m), b), mul_(d, c));
		lemma_eq_ref(b);
		cong_mul_(mod_(d, m), b, mod_(add_(d, mul_(mul_(add_(c, c), sub_(a, a)), m)), m), b);
		lemma_eq_ref(mul_(d, c));
	}
	let temp_82_0 = (mul_((mul_(b, d)), (mul_(b, b))));
	let temp_82_1 = (mul_((mul_(b, b)), (mul_(b, d))));
	assert(eq_(temp_82_0, temp_82_1)) by {
		lemma_mul_comm(mul_(b, d), mul_(b, b));
	}
	let temp_83_0 = (mul_((mul_(c, c)), (mul_(a, c))));
	let temp_83_1 = (mul_((mul_(a, c)), (mul_(c, c))));
	assert(eq_(temp_83_0, temp_83_1)) by {
		lemma_mul_comm(mul_(c, c), mul_(a, c));
	}
	let temp_84_0 = (add_((mul_(a, d)), (mul_(b, c))));
	let temp_84_1 = (add_((mul_(d, a)), (mul_(b, c))));
	assert(eq_(temp_84_0, temp_84_1)) by {
		cong_add_(mul_(a, d), mul_(b, c), mul_(d, a), mul_(b, c));
		lemma_mul_comm(a, d);
		lemma_eq_ref(mul_(b, c));
	}
	let temp_85_0 = (mul_((mul_(a, c)), (mod_((mul_(c, b)), m))));
	let temp_85_1 = (mul_((mul_(a, c)), (mod_((mul_(b, c)), m))));
	assert(eq_(temp_85_0, temp_85_1)) by {
		lemma_mul_comm(c, b);
		cong_mul_(mul_(a, c), mod_(mul_(c, b), m), mul_(a, c), mod_(mul_(b, c), m));
		lemma_eq_ref(mul_(a, c));
		cong_mod_(mul_(c, b), m, mul_(b, c), m);
		lemma_eq_ref(m);
	}
	let temp_86_0 = (mul_((mul_(b, d)), (add_(b, b))));
	let temp_86_1 = (mul_((mul_(b, d)), (add_(b, b))));
	assert(eq_(temp_86_0, temp_86_1)) by {
		lemma_eq_ref(temp_86_0);
	}
	let temp_87_0 = (mul_((mul_(d, c)), (mul_((mod_(d, m)), (mod_(a, m))))));
	let temp_87_1 = (mul_((mul_(d, c)), (mul_((mod_(d, m)), (mod_((sub_(a, (mul_((mod_((mul_((mul_(d, d)), (sub_(b, a)))), m)), m)))), m))))));
	assert(eq_(temp_87_0, temp_87_1)) by {
		lemma_eq_ref(mul_(d, c));
		cong_mul_(mod_(d, m), mod_(a, m), mod_(d, m), mod_(sub_(a, mul_(mod_(mul_(mul_(d, d), sub_(b, a)), m), m)), m));
		lemma_eq_ref(mod_(d, m));
		cong_mul_(mul_(d, c), mul_(mod_(d, m), mod_(a, m)), mul_(d, c), mul_(mod_(d, m), mod_(sub_(a, mul_(mod_(mul_(mul_(d, d), sub_(b, a)), m), m)), m)));
		lemma_mod_mul_vanish(a, mod_(mul_(mul_(d, d), sub_(b, a)), m), m);
	}
	let temp_88_0 = (add_((mul_(as_elem(50), (mod_(b, m)))), (mod_((mul_(a, d)), m))));
	let temp_88_1 = (add_((mod_((mul_(a, d)), m)), (mul_(as_elem(50), (mod_(b, m))))));
	assert(eq_(temp_88_0, temp_88_1)) by {
		lemma_add_comm(mul_(as_elem(50), mod_(b, m)), mod_(mul_(a, d), m));
	}
	let temp_89_0 = (mod_((mul_((mul_(c, a)), (mul_(a, b)))), m));
	let temp_89_1 = (mod_((mul_((mul_((mul_(c, a)), a)), b)), m));
	assert(eq_(temp_89_0, temp_89_1)) by {
		lemma_mul_assoc(mul_(c, a), a, b);
		cong_mod_(mul_(mul_(c, a), mul_(a, b)), m, mul_(mul_(mul_(c, a), a), b), m);
		lemma_eq_ref(m);
	}
	let temp_90_0 = (sub_((mod_((mul_(b, b)), m)), (mul_(d, b))));
	let temp_90_1 = (sub_((mod_((sub_((mul_(b, b)), (mul_((mul_((mul_(a, (mod_(c, m)))), (sub_(b, b)))), m)))), m)), (mul_(d, b))));
	assert(eq_(temp_90_0, temp_90_1)) by {
		lemma_mod_mul_vanish(mul_(b, b), mul_(mul_(a, mod_(c, m)), sub_(b, b)), m);
		cong_sub_(mod_(mul_(b, b), m), mul_(d, b), mod_(sub_(mul_(b, b), mul_(mul_(mul_(a, mod_(c, m)), sub_(b, b)), m)), m), mul_(d, b));
		lemma_eq_ref(mul_(d, b));
	}
	let temp_91_0 = (sub_((mul_((mod_(d, m)), c)), (mul_((mod_(b, m)), b))));
	let temp_91_1 = (sub_((mul_((mod_(d, m)), c)), (mul_((mod_((add_(b, (mul_((mul_((mul_(d, c)), (mul_((mod_(c, m)), b)))), m)))), m)), b))));
	assert(eq_(temp_91_0, temp_91_1)) by {
		lemma_mod_mul_vanish(b, mul_(mul_(d, c), mul_(mod_(c, m), b)), m);
		cong_sub_(mul_(mod_(d, m), c), mul_(mod_(b, m), b), mul_(mod_(d, m), c), mul_(mod_(add_(b, mul_(mul_(mul_(d, c), mul_(mod_(c, m), b)), m)), m), b));
		lemma_eq_ref(b);
		lemma_eq_ref(mul_(mod_(d, m), c));
		cong_mul_(mod_(b, m), b, mod_(add_(b, mul_(mul_(mul_(d, c), mul_(mod_(c, m), b)), m)), m), b);
	}
	let temp_92_0 = (mul_((mul_(d, a)), (add_(a, a))));
	let temp_92_1 = (mul_((mul_(d, a)), (add_(a, a))));
	assert(eq_(temp_92_0, temp_92_1)) by {
		lemma_eq_ref(temp_92_0);
	}
	let temp_93_0 = (mod_((mul_((mul_(as_elem(48), d)), (mul_(b, b)))), m));
	let temp_93_1 = (mod_((add_((mul_((mul_((mul_((mod_(b, m)), d)), (mul_(c, a)))), m)), (mul_((mul_(as_elem(48), d)), (mul_(b, b)))))), m));
	assert(eq_(temp_93_0, temp_93_1)) by {
		lemma_mod_mul_vanish(mul_(mul_(as_elem(48), d), mul_(b, b)), mul_(mul_(mod_(b, m), d), mul_(c, a)), m);
	}
	let temp_94_0 = (mul_((mul_(d, b)), (mul_(d, d))));
	let temp_94_1 = (mul_(d, (mul_(b, (mul_(d, d))))));
	assert(eq_(temp_94_0, temp_94_1)) by {
		lemma_eq_sym(temp_94_1, temp_94_0);
		lemma_mul_assoc(d, b, mul_(d, d));
	}
	let temp_95_0 = (mul_((mul_((mod_(c, m)), c)), (mul_(a, d))));
	let temp_95_1 = (mul_((mul_((mod_((add_((mul_((mul_((mul_(c, (mod_(b, m)))), (sub_(b, c)))), m)), c)), m)), c)), (mul_(a, d))));
	assert(eq_(temp_95_0, temp_95_1)) by {
		lemma_mod_mul_vanish(c, mul_(mul_(c, mod_(b, m)), sub_(b, c)), m);
		cong_mul_(mul_(mod_(c, m), c), mul_(a, d), mul_(mod_(add_(mul_(mul_(mul_(c, mod_(b, m)), sub_(b, c)), m), c), m), c), mul_(a, d));
		lemma_eq_ref(c);
		cong_mul_(mod_(c, m), c, mod_(add_(mul_(mul_(mul_(c, mod_(b, m)), sub_(b, c)), m), c), m), c);
		lemma_eq_ref(mul_(a, d));
	}
	let temp_96_0 = (mul_((mod_((mul_(d, d)), m)), (mod_((mul_(c, c)), m))));
	let temp_96_1 = (mul_((mod_((add_((mul_(d, d)), (mul_((mul_((mul_(b, c)), (mul_(a, a)))), m)))), m)), (mod_((mul_(c, c)), m))));
	assert(eq_(temp_96_0, temp_96_1)) by {
		lemma_mod_mul_vanish(mul_(d, d), mul_(mul_(b, c), mul_(a, a)), m);
		cong_mul_(mod_(mul_(d, d), m), mod_(mul_(c, c), m), mod_(add_(mul_(d, d), mul_(mul_(mul_(b, c), mul_(a, a)), m)), m), mod_(mul_(c, c), m));
		lemma_eq_ref(mod_(mul_(c, c), m));
	}
	let temp_97_0 = (mul_((mul_(c, d)), (mul_(b, b))));
	let temp_97_1 = (mul_((mul_(b, b)), (mul_(c, d))));
	assert(eq_(temp_97_0, temp_97_1)) by {
		lemma_mul_comm(mul_(c, d), mul_(b, b));
	}
	let temp_98_0 = (add_((mul_(b, a)), (mul_(d, a))));
	let temp_98_1 = (add_((mul_(d, a)), (mul_(b, a))));
	assert(eq_(temp_98_0, temp_98_1)) by {
		lemma_add_comm(mul_(b, a), mul_(d, a));
	}
	let temp_99_0 = (mul_((mul_(a, a)), (mul_(c, b))));
	let temp_99_1 = (mul_((mul_(a, a)), (mul_(b, c))));
	assert(eq_(temp_99_0, temp_99_1)) by {
		cong_mul_(mul_(a, a), mul_(c, b), mul_(a, a), mul_(b, c));
		lemma_mul_comm(a, a);
		lemma_mul_comm(c, b);
	}
	let temp_100_0 = (mul_((mul_(d, a)), (mul_(d, b))));
	let temp_100_1 = (mul_((mul_((mul_(d, a)), d)), b));
	assert(eq_(temp_100_0, temp_100_1)) by {
		lemma_mul_assoc(mul_(d, a), d, b);
	}
	let temp_101_0 = (mul_((mul_(c, a)), (mul_(d, (mod_(d, m))))));
	let temp_101_1 = (mul_((mul_(a, c)), (mul_(d, (mod_(d, m))))));
	assert(eq_(temp_101_0, temp_101_1)) by {
		lemma_mul_comm(c, a);
		cong_mul_(mul_(c, a), mul_(d, mod_(d, m)), mul_(a, c), mul_(d, mod_(d, m)));
		lemma_eq_ref(mul_(d, mod_(d, m)));
	}
	let temp_102_0 = (mul_((sub_((mod_(b, m)), d)), (mul_(a, d))));
	let temp_102_1 = (mul_((sub_((mod_(b, m)), d)), (mul_(d, a))));
	assert(eq_(temp_102_0, temp_102_1)) by {
		lemma_mul_comm(a, d);
		cong_mul_(sub_(mod_(b, m), d), mul_(a, d), sub_(mod_(b, m), d), mul_(d, a));
		lemma_eq_ref(sub_(mod_(b, m), d));
	}
	let temp_103_0 = (mul_((mod_((mul_((mod_(c, m)), d)), m)), (mul_(b, a))));
	let temp_103_1 = (mul_((mul_(b, a)), (mod_((mul_((mod_(c, m)), d)), m))));
	assert(eq_(temp_103_0, temp_103_1)) by {
		lemma_mul_comm(mod_(mul_(mod_(c, m), d), m), mul_(b, a));
	}
	let temp_104_0 = (mul_((mul_((mod_(d, m)), a)), (add_(d, d))));
	let temp_104_1 = (mul_((mod_(d, m)), (mul_(a, (add_(d, d))))));
	assert(eq_(temp_104_0, temp_104_1)) by {
		lemma_eq_sym(temp_104_1, temp_104_0);
		lemma_mul_assoc(mod_(d, m), a, add_(d, d));
	}
	let temp_105_0 = (mul_((mul_(b, d)), (mod_((mul_(a, d)), m))));
	let temp_105_1 = (mul_((mul_(b, d)), (mod_((sub_((mul_(a, d)), (mul_((mul_((mul_(d, a)), (mul_(c, b)))), m)))), m))));
	assert(eq_(temp_105_0, temp_105_1)) by {
		lemma_mod_mul_vanish(mul_(a, d), mul_(mul_(d, a), mul_(c, b)), m);
		cong_mul_(mul_(b, d), mod_(mul_(a, d), m), mul_(b, d), mod_(sub_(mul_(a, d), mul_(mul_(mul_(d, a), mul_(c, b)), m)), m));
		lemma_eq_ref(mul_(b, d));
	}
	let temp_106_0 = (mul_((mul_(d, d)), (mul_((mod_(a, m)), d))));
	let temp_106_1 = (mul_(d, (mul_(d, (mul_((mod_(a, m)), d))))));
	assert(eq_(temp_106_0, temp_106_1)) by {
		lemma_eq_sym(temp_106_1, temp_106_0);
		lemma_mul_assoc(d, d, mul_(mod_(a, m), d));
	}
	let temp_107_0 = (mul_((sub_(b, c)), (mul_(c, as_elem(79)))));
	let temp_107_1 = (mul_((mul_((sub_(b, c)), c)), as_elem(79)));
	assert(eq_(temp_107_0, temp_107_1)) by {
		lemma_mul_assoc(sub_(b, c), c, as_elem(79));
	}
	let temp_108_0 = (add_((mul_(a, b)), (mul_((mod_(a, m)), c))));
	let temp_108_1 = (add_((mul_(a, b)), (mul_((mod_((add_((mul_((mul_((mul_(b, a)), (mul_(d, c)))), m)), a)), m)), c))));
	assert(eq_(temp_108_0, temp_108_1)) by {
		lemma_mod_mul_vanish(a, mul_(mul_(b, a), mul_(d, c)), m);
		cong_add_(mul_(a, b), mul_(mod_(a, m), c), mul_(a, b), mul_(mod_(add_(mul_(mul_(mul_(b, a), mul_(d, c)), m), a), m), c));
		lemma_eq_ref(mul_(a, b));
		lemma_eq_ref(c);
		cong_mul_(mod_(a, m), c, mod_(add_(mul_(mul_(mul_(b, a), mul_(d, c)), m), a), m), c);
	}
	let temp_109_0 = (mul_((mod_((mul_(b, c)), m)), (mul_(c, (mod_(d, m))))));
	let temp_109_1 = (mul_((mul_((mod_((mul_(b, c)), m)), c)), (mod_(d, m))));
	assert(eq_(temp_109_0, temp_109_1)) by {
		lemma_mul_assoc(mod_(mul_(b, c), m), c, mod_(d, m));
	}

}

} // verus!