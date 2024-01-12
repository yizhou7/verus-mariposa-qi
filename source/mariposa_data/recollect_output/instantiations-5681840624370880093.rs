use builtin_macros::*;
// use builtin::*;
mod nl_basics;
use crate::nl_basics::*;
verus! {

pub proof fn free_0(a: Elem, b: Elem, c: Elem, d: Elem, m: Elem)
{
	let temp_0_0 = (mul_((mul_(b, b)), (mul_(b, a))));
	let temp_0_1 = (mul_((mul_(b, b)), (mul_(b, a))));
	assert(eq_(temp_0_0, temp_0_1)) by {
		lemma_eq_ref(temp_0_0);
	}
	let temp_1_0 = (add_((mul_(d, a)), (mod_((mul_(c, d)), m))));
	let temp_1_1 = (add_((mul_(d, a)), (mod_((mul_(d, c)), m))));
	assert(eq_(temp_1_0, temp_1_1)) by {
		lemma_mul_comm(c, d);
		cong_add_(mul_(d, a), mod_(mul_(c, d), m), mul_(d, a), mod_(mul_(d, c), m));
		lemma_eq_ref(m);
		lemma_eq_ref(mul_(d, a));
		cong_mod_(mul_(c, d), m, mul_(d, c), m);
	}
	let temp_2_0 = (mul_((mul_(a, c)), (mul_(a, c))));
	let temp_2_1 = (mul_((mul_(a, c)), (mul_(a, c))));
	assert(eq_(temp_2_0, temp_2_1)) by {
		lemma_eq_ref(temp_2_0);
	}
	let temp_3_0 = (mul_((mul_(a, a)), (mul_(d, d))));
	let temp_3_1 = (mul_((mul_((mul_(a, a)), d)), d));
	assert(eq_(temp_3_0, temp_3_1)) by {
		lemma_mul_assoc(mul_(a, a), d, d);
	}
	let temp_4_0 = (mod_((mul_((sub_((mod_(a, m)), c)), (mul_(b, b)))), m));
	let temp_4_1 = (mod_((mul_((mul_((sub_((mod_(a, m)), c)), b)), b)), m));
	assert(eq_(temp_4_0, temp_4_1)) by {
		lemma_mul_assoc(sub_(mod_(a, m), c), b, b);
		cong_mod_(mul_(sub_(mod_(a, m), c), mul_(b, b)), m, mul_(mul_(sub_(mod_(a, m), c), b), b), m);
		lemma_eq_ref(m);
	}
	let temp_5_0 = (add_((mul_((mod_(d, m)), c)), (mod_((mul_(b, b)), m))));
	let temp_5_1 = (add_((mul_((mod_((add_((mul_((add_((mul_(d, a)), (sub_(d, b)))), m)), d)), m)), c)), (mod_((mul_(b, b)), m))));
	assert(eq_(temp_5_0, temp_5_1)) by {
		lemma_mod_mul_vanish(d, add_(mul_(d, a), sub_(d, b)), m);
		cong_add_(mul_(mod_(d, m), c), mod_(mul_(b, b), m), mul_(mod_(add_(mul_(add_(mul_(d, a), sub_(d, b)), m), d), m), c), mod_(mul_(b, b), m));
		lemma_eq_ref(c);
		cong_mul_(mod_(d, m), c, mod_(add_(mul_(add_(mul_(d, a), sub_(d, b)), m), d), m), c);
		lemma_eq_ref(mod_(mul_(b, b), m));
	}
	let temp_6_0 = (mul_((sub_(b, (mod_(a, m)))), (mul_(c, c))));
	let temp_6_1 = (mul_((mul_((sub_(b, (mod_(a, m)))), c)), c));
	assert(eq_(temp_6_0, temp_6_1)) by {
		lemma_mul_assoc(sub_(b, mod_(a, m)), c, c);
	}
	let temp_7_0 = (mul_((mul_((mod_(d, m)), (mod_(b, m)))), (sub_(c, d))));
	let temp_7_1 = (mul_((mul_((mod_((add_(d, (mul_((mul_((mul_(d, a)), (mul_(d, b)))), m)))), m)), (mod_(b, m)))), (sub_(c, d))));
	assert(eq_(temp_7_0, temp_7_1)) by {
		lemma_mod_mul_vanish(d, mul_(mul_(d, a), mul_(d, b)), m);
		cong_mul_(mul_(mod_(d, m), mod_(b, m)), sub_(c, d), mul_(mod_(add_(d, mul_(mul_(mul_(d, a), mul_(d, b)), m)), m), mod_(b, m)), sub_(c, d));
		lemma_eq_ref(mod_(b, m));
		cong_mul_(mod_(d, m), mod_(b, m), mod_(add_(d, mul_(mul_(mul_(d, a), mul_(d, b)), m)), m), mod_(b, m));
		lemma_eq_ref(sub_(c, d));
	}
	let temp_8_0 = (mul_((mul_(b, b)), (mul_(a, c))));
	let temp_8_1 = (mul_((mul_((mul_(b, b)), a)), c));
	assert(eq_(temp_8_0, temp_8_1)) by {
		lemma_mul_assoc(mul_(b, b), a, c);
	}
	let temp_9_0 = (mod_((mul_((mod_((sub_(d, c)), m)), (add_(a, d)))), m));
	let temp_9_1 = (mod_((add_((mul_((mod_((sub_(d, c)), m)), a)), (mul_((mod_((sub_(d, c)), m)), d)))), m));
	assert(eq_(temp_9_0, temp_9_1)) by {
		lemma_mul_dist(mod_(sub_(d, c), m), a, d);
		cong_mod_(mul_(mod_(sub_(d, c), m), add_(a, d)), m, add_(mul_(mod_(sub_(d, c), m), a), mul_(mod_(sub_(d, c), m), d)), m);
		lemma_eq_ref(m);
	}
	let temp_10_0 = (mod_((add_((mul_(b, a)), (add_(d, d)))), m));
	let temp_10_1 = (mod_((sub_((add_((mul_(b, a)), (add_(d, d)))), (mul_((sub_((mul_(a, c)), (mul_(a, c)))), m)))), m));
	assert(eq_(temp_10_0, temp_10_1)) by {
		lemma_mod_mul_vanish(add_(mul_(b, a), add_(d, d)), sub_(mul_(a, c), mul_(a, c)), m);
	}
	let temp_11_0 = (mod_((mul_((mul_(a, b)), (mul_(a, a)))), m));
	let temp_11_1 = (mod_((mul_((mul_((mul_(a, b)), a)), a)), m));
	assert(eq_(temp_11_0, temp_11_1)) by {
		lemma_mul_assoc(mul_(a, b), a, a);
		cong_mod_(mul_(mul_(a, b), mul_(a, a)), m, mul_(mul_(mul_(a, b), a), a), m);
		lemma_eq_ref(m);
	}
	let temp_12_0 = (add_((mul_(a, c)), (mul_(d, d))));
	let temp_12_1 = (add_((mul_(d, d)), (mul_(a, c))));
	assert(eq_(temp_12_0, temp_12_1)) by {
		lemma_add_comm(mul_(a, c), mul_(d, d));
	}
	let temp_13_0 = (mul_((mul_(as_elem(71), b)), (mul_(b, c))));
	let temp_13_1 = (mul_(as_elem(71), (mul_(b, (mul_(b, c))))));
	assert(eq_(temp_13_0, temp_13_1)) by {
		lemma_eq_sym(temp_13_1, temp_13_0);
		lemma_mul_assoc(as_elem(71), b, mul_(b, c));
	}
	let temp_14_0 = (add_(d, (mul_(d, a))));
	let temp_14_1 = (add_((mul_(d, a)), d));
	assert(eq_(temp_14_0, temp_14_1)) by {
		lemma_add_comm(d, mul_(d, a));
	}
	let temp_15_0 = (add_((mul_(a, d)), (sub_(a, b))));
	let temp_15_1 = (add_((sub_(a, b)), (mul_(a, d))));
	assert(eq_(temp_15_0, temp_15_1)) by {
		lemma_add_comm(mul_(a, d), sub_(a, b));
	}
	let temp_16_0 = (mul_((mul_(c, c)), (add_(a, b))));
	let temp_16_1 = (mul_((mul_(c, c)), (add_(b, a))));
	assert(eq_(temp_16_0, temp_16_1)) by {
		cong_mul_(mul_(c, c), add_(a, b), mul_(c, c), add_(b, a));
		lemma_add_comm(a, b);
		lemma_mul_comm(c, c);
	}
	let temp_17_0 = (mul_((mul_(b, b)), (mul_(d, a))));
	let temp_17_1 = (mul_((mul_((mul_(b, b)), d)), a));
	assert(eq_(temp_17_0, temp_17_1)) by {
		lemma_mul_assoc(mul_(b, b), d, a);
	}
	let temp_18_0 = (mul_((mul_(a, d)), (mod_((mul_(b, c)), m))));
	let temp_18_1 = (mul_((mod_((mul_(b, c)), m)), (mul_(a, d))));
	assert(eq_(temp_18_0, temp_18_1)) by {
		lemma_mul_comm(mul_(a, d), mod_(mul_(b, c), m));
	}
	let temp_19_0 = (mul_((sub_(a, as_elem(79))), (mod_((mul_(b, (mod_(b, m)))), m))));
	let temp_19_1 = (sub_((mul_(a, (mod_((mul_(b, (mod_(b, m)))), m)))), (mul_(as_elem(79), (mod_((mul_(b, (mod_(b, m)))), m))))));
	assert(eq_(temp_19_0, temp_19_1)) by {
		lemma_mul_dist(mod_(mul_(b, mod_(b, m)), m), a, as_elem(79));
	}
	let temp_20_0 = (mul_((mod_((add_(d, d)), m)), (mul_(a, d))));
	let temp_20_1 = (mul_((mod_((add_(d, d)), m)), (mul_(a, d))));
	assert(eq_(temp_20_0, temp_20_1)) by {
		lemma_eq_ref(temp_20_0);
	}
	let temp_21_0 = (mul_((mul_(b, c)), (mul_(a, b))));
	let temp_21_1 = (mul_(b, (mul_(c, (mul_(a, b))))));
	assert(eq_(temp_21_0, temp_21_1)) by {
		lemma_eq_sym(temp_21_1, temp_21_0);
		lemma_mul_assoc(b, c, mul_(a, b));
	}
	let temp_22_0 = (add_((mul_(a, c)), (mul_(b, c))));
	let temp_22_1 = (mul_((add_(a, b)), c));
	assert(eq_(temp_22_0, temp_22_1)) by {
		lemma_eq_sym(temp_22_1, temp_22_0);
		lemma_mul_dist(a, b, c);
	}
	let temp_23_0 = (mul_((mul_(c, (mod_(c, m)))), (mul_((mod_(b, m)), c))));
	let temp_23_1 = (mul_(c, (mul_((mod_(c, m)), (mul_((mod_(b, m)), c))))));
	assert(eq_(temp_23_0, temp_23_1)) by {
		lemma_mul_assoc(c, mod_(c, m), mul_(mod_(b, m), c));
		lemma_eq_sym(temp_23_1, temp_23_0);
	}
	let temp_24_0 = (mod_((add_((add_(c, c)), (mul_(c, c)))), m));
	let temp_24_1 = (mod_((add_((add_((add_(c, c)), (mul_(c, c)))), (mul_((add_((mul_(d, d)), (sub_(a, d)))), m)))), m));
	assert(eq_(temp_24_0, temp_24_1)) by {
		lemma_mod_mul_vanish(add_(add_(c, c), mul_(c, c)), add_(mul_(d, d), sub_(a, d)), m);
	}
	let temp_25_0 = (mul_((mul_(c, b)), (add_(as_elem(85), as_elem(96)))));
	let temp_25_1 = (mul_((mul_(c, b)), (add_(as_elem(96), as_elem(85)))));
	assert(eq_(temp_25_0, temp_25_1)) by {
		lemma_add_comm(as_elem(85), as_elem(96));
		cong_mul_(mul_(c, b), add_(as_elem(85), as_elem(96)), mul_(c, b), add_(as_elem(96), as_elem(85)));
		lemma_eq_ref(mul_(c, b));
	}
	let temp_26_0 = (mul_((add_(a, as_elem(96))), (mul_(a, a))));
	let temp_26_1 = (mul_((add_(as_elem(96), a)), (mul_(a, a))));
	assert(eq_(temp_26_0, temp_26_1)) by {
		cong_mul_(add_(a, as_elem(96)), mul_(a, a), add_(as_elem(96), a), mul_(a, a));
		lemma_add_comm(a, as_elem(96));
		lemma_mul_comm(a, a);
	}
	let temp_27_0 = (mod_((mul_((mul_(d, d)), (mul_(c, a)))), m));
	let temp_27_1 = (mod_((mul_(d, (mul_(d, (mul_(c, a)))))), m));
	assert(eq_(temp_27_0, temp_27_1)) by {
		lemma_mul_assoc(d, d, mul_(c, a));
		cong_mod_(mul_(mul_(d, d), mul_(c, a)), m, mul_(d, mul_(d, mul_(c, a))), m);
		lemma_eq_sym(mul_(d, mul_(d, mul_(c, a))), mul_(mul_(d, d), mul_(c, a)));
		lemma_eq_ref(m);
	}
	let temp_28_0 = (mul_((mul_(b, a)), (add_(c, d))));
	let temp_28_1 = (mul_((add_(c, d)), (mul_(b, a))));
	assert(eq_(temp_28_0, temp_28_1)) by {
		lemma_mul_comm(mul_(b, a), add_(c, d));
	}
	let temp_29_0 = (mul_((mul_(c, b)), (sub_(a, a))));
	let temp_29_1 = (mul_((sub_(a, a)), (mul_(c, b))));
	assert(eq_(temp_29_0, temp_29_1)) by {
		lemma_mul_comm(mul_(c, b), sub_(a, a));
	}
	let temp_30_0 = (sub_((mod_((mul_(c, d)), m)), c));
	let temp_30_1 = (sub_((mod_((sub_((mul_(c, d)), (mul_((add_((mul_(a, b)), (mul_(b, a)))), m)))), m)), c));
	assert(eq_(temp_30_0, temp_30_1)) by {
		lemma_mod_mul_vanish(mul_(c, d), add_(mul_(a, b), mul_(b, a)), m);
		cong_sub_(mod_(mul_(c, d), m), c, mod_(sub_(mul_(c, d), mul_(add_(mul_(a, b), mul_(b, a)), m)), m), c);
		lemma_eq_ref(c);
	}
	let temp_31_0 = (add_((mul_(c, (mod_(a, m)))), (add_(d, b))));
	let temp_31_1 = (add_((mul_(c, (mod_(a, m)))), (add_(b, d))));
	assert(eq_(temp_31_0, temp_31_1)) by {
		lemma_add_comm(d, b);
		cong_add_(mul_(c, mod_(a, m)), add_(d, b), mul_(c, mod_(a, m)), add_(b, d));
		lemma_eq_ref(mul_(c, mod_(a, m)));
	}
	let temp_32_0 = (mul_((mul_(c, b)), (add_(d, as_elem(80)))));
	let temp_32_1 = (mul_(c, (mul_(b, (add_(d, as_elem(80)))))));
	assert(eq_(temp_32_0, temp_32_1)) by {
		lemma_mul_assoc(c, b, add_(d, as_elem(80)));
		lemma_eq_sym(temp_32_1, temp_32_0);
	}
	let temp_33_0 = (mod_((mul_(a, (mul_(b, a)))), m));
	let temp_33_1 = (mod_((mul_((mul_(a, b)), a)), m));
	assert(eq_(temp_33_0, temp_33_1)) by {
		cong_mod_(mul_(a, mul_(b, a)), m, mul_(mul_(a, b), a), m);
		lemma_mul_assoc(a, b, a);
		lemma_eq_ref(m);
	}
	let temp_34_0 = (sub_((mul_(b, c)), (mul_(c, d))));
	let temp_34_1 = (sub_((mul_(b, c)), (mul_(d, c))));
	assert(eq_(temp_34_0, temp_34_1)) by {
		cong_sub_(mul_(b, c), mul_(c, d), mul_(b, c), mul_(d, c));
		lemma_mul_comm(c, d);
		lemma_eq_ref(mul_(b, c));
	}
	let temp_35_0 = (mod_((mul_((mod_((mul_(c, c)), m)), (mod_((mul_(a, b)), m)))), m));
	let temp_35_1 = (mod_((mod_((mul_((mul_(a, b)), (mod_((mul_(c, c)), m)))), m)), m));
	assert(eq_(temp_35_0, temp_35_1)) by {
		lemma_mod_mul_noop(mul_(a, b), mod_(mul_(c, c), m), m);
		lemma_eq_sym(temp_35_1, temp_35_0);
	}
	let temp_36_0 = (mul_((sub_(b, c)), (add_(d, c))));
	let temp_36_1 = (mul_((add_(d, c)), (sub_(b, c))));
	assert(eq_(temp_36_0, temp_36_1)) by {
		lemma_mul_comm(sub_(b, c), add_(d, c));
	}
	let temp_37_0 = (mul_((mul_(d, c)), (mod_((mul_(d, d)), m))));
	let temp_37_1 = (mul_((mul_(c, d)), (mod_((mul_(d, d)), m))));
	assert(eq_(temp_37_0, temp_37_1)) by {
		cong_mul_(mul_(d, c), mod_(mul_(d, d), m), mul_(c, d), mod_(mul_(d, d), m));
		lemma_mul_comm(d, c);
		lemma_eq_ref(mod_(mul_(d, d), m));
	}
	let temp_38_0 = (mod_((mul_((mul_(d, d)), (mod_((mul_(c, b)), m)))), m));
	let temp_38_1 = (mod_((add_((mul_((mul_(d, d)), (mod_((mul_(c, b)), m)))), (mul_((mul_((sub_((mod_(a, m)), b)), (mul_(b, a)))), m)))), m));
	assert(eq_(temp_38_0, temp_38_1)) by {
		lemma_mod_mul_vanish(mul_(mul_(d, d), mod_(mul_(c, b), m)), mul_(sub_(mod_(a, m), b), mul_(b, a)), m);
	}
	let temp_39_0 = (mul_((mul_(as_elem(58), a)), (mul_((mod_(c, m)), d))));
	let temp_39_1 = (mul_((mul_((mod_(c, m)), d)), (mul_(as_elem(58), a))));
	assert(eq_(temp_39_0, temp_39_1)) by {
		lemma_mul_comm(mul_(as_elem(58), a), mul_(mod_(c, m), d));
	}
	let temp_40_0 = (sub_((sub_(b, b)), (mul_(d, d))));
	let temp_40_1 = (sub_((sub_(b, b)), (mul_(d, d))));
	assert(eq_(temp_40_0, temp_40_1)) by {
		lemma_eq_ref(temp_40_0);
	}
	let temp_41_0 = (mul_((mul_(a, b)), (mul_(d, d))));
	let temp_41_1 = (mul_(a, (mul_(b, (mul_(d, d))))));
	assert(eq_(temp_41_0, temp_41_1)) by {
		lemma_eq_sym(temp_41_1, temp_41_0);
		lemma_mul_assoc(a, b, mul_(d, d));
	}
	let temp_42_0 = (mul_((mul_(a, c)), (sub_(b, a))));
	let temp_42_1 = (mul_((mul_(c, a)), (sub_(b, a))));
	assert(eq_(temp_42_0, temp_42_1)) by {
		cong_mul_(mul_(a, c), sub_(b, a), mul_(c, a), sub_(b, a));
		lemma_mul_comm(a, c);
		lemma_eq_ref(sub_(b, a));
	}
	let temp_43_0 = (mul_((mul_(a, d)), (sub_(d, a))));
	let temp_43_1 = (mul_((sub_(d, a)), (mul_(a, d))));
	assert(eq_(temp_43_0, temp_43_1)) by {
		lemma_mul_comm(mul_(a, d), sub_(d, a));
	}
	let temp_44_0 = (mod_((mul_((mul_(a, c)), (mul_(a, a)))), m));
	let temp_44_1 = (mod_((mul_((mul_(a, c)), (mul_(a, a)))), m));
	assert(eq_(temp_44_0, temp_44_1)) by {
		lemma_eq_ref(temp_44_0);
	}
	let temp_45_0 = (mul_((mul_(d, d)), (mul_(d, (mod_(d, m))))));
	let temp_45_1 = (mul_((mul_(d, d)), (mul_(d, (mod_(d, m))))));
	assert(eq_(temp_45_0, temp_45_1)) by {
		lemma_eq_ref(temp_45_0);
	}
	let temp_46_0 = (mul_((mul_(d, c)), (mul_(c, c))));
	let temp_46_1 = (mul_((mul_((mul_(d, c)), c)), c));
	assert(eq_(temp_46_0, temp_46_1)) by {
		lemma_mul_assoc(mul_(d, c), c, c);
	}
	let temp_47_0 = (mul_((mul_(d, d)), (mod_((mul_(b, c)), m))));
	let temp_47_1 = (mul_(d, (mul_(d, (mod_((mul_(b, c)), m))))));
	assert(eq_(temp_47_0, temp_47_1)) by {
		lemma_mul_assoc(d, d, mod_(mul_(b, c), m));
		lemma_eq_sym(temp_47_1, temp_47_0);
	}
	let temp_48_0 = (mul_((mul_(a, a)), (mul_(b, d))));
	let temp_48_1 = (mul_((mul_(b, d)), (mul_(a, a))));
	assert(eq_(temp_48_0, temp_48_1)) by {
		lemma_mul_comm(mul_(a, a), mul_(b, d));
	}
	let temp_49_0 = (mul_((mul_(c, (mod_(a, m)))), (mul_(b, b))));
	let temp_49_1 = (mul_((mul_(c, (mod_((sub_(a, (mul_((mul_((sub_(b, a)), (mod_((sub_(c, a)), m)))), m)))), m)))), (mul_(b, b))));
	assert(eq_(temp_49_0, temp_49_1)) by {
		lemma_mul_comm(b, b);
		lemma_mod_mul_vanish(a, mul_(sub_(b, a), mod_(sub_(c, a), m)), m);
		cong_mul_(mul_(c, mod_(a, m)), mul_(b, b), mul_(c, mod_(sub_(a, mul_(mul_(sub_(b, a), mod_(sub_(c, a), m)), m)), m)), mul_(b, b));
		lemma_eq_ref(c);
		cong_mul_(c, mod_(a, m), c, mod_(sub_(a, mul_(mul_(sub_(b, a), mod_(sub_(c, a), m)), m)), m));
	}
	let temp_50_0 = (mul_((mul_(a, as_elem(12))), (add_(c, (mod_(c, m))))));
	let temp_50_1 = (mul_((mul_(as_elem(12), a)), (add_(c, (mod_(c, m))))));
	assert(eq_(temp_50_0, temp_50_1)) by {
		lemma_mul_comm(a, as_elem(12));
		cong_mul_(mul_(a, as_elem(12)), add_(c, mod_(c, m)), mul_(as_elem(12), a), add_(c, mod_(c, m)));
		lemma_eq_ref(add_(c, mod_(c, m)));
	}
	let temp_51_0 = (mul_((mul_(c, c)), (mul_((mod_(d, m)), b))));
	let temp_51_1 = (mul_((mul_(c, c)), (mul_(b, (mod_(d, m))))));
	assert(eq_(temp_51_0, temp_51_1)) by {
		lemma_mul_comm(c, c);
		lemma_mul_comm(mod_(d, m), b);
		cong_mul_(mul_(c, c), mul_(mod_(d, m), b), mul_(c, c), mul_(b, mod_(d, m)));
	}
	let temp_52_0 = (mul_((sub_(c, c)), (mod_((add_(c, b)), m))));
	let temp_52_1 = (sub_((mul_(c, (mod_((add_(c, b)), m)))), (mul_(c, (mod_((add_(c, b)), m))))));
	assert(eq_(temp_52_0, temp_52_1)) by {
		lemma_mul_dist(mod_(add_(c, b), m), c, c);
	}
	let temp_53_0 = (mul_((mul_(b, d)), (mul_(d, c))));
	let temp_53_1 = (mul_((mul_((mul_(b, d)), d)), c));
	assert(eq_(temp_53_0, temp_53_1)) by {
		lemma_mul_assoc(mul_(b, d), d, c);
	}
	let temp_54_0 = (mul_((mul_(d, d)), (mul_(d, d))));
	let temp_54_1 = (mul_((mul_((mul_(d, d)), d)), d));
	assert(eq_(temp_54_0, temp_54_1)) by {
		lemma_mul_assoc(mul_(d, d), d, d);
	}
	let temp_55_0 = (mul_((mul_((mod_(b, m)), (mod_(a, m)))), (mul_(as_elem(20), a))));
	let temp_55_1 = (mul_((mod_(b, m)), (mul_((mod_(a, m)), (mul_(as_elem(20), a))))));
	assert(eq_(temp_55_0, temp_55_1)) by {
		lemma_mul_assoc(mod_(b, m), mod_(a, m), mul_(as_elem(20), a));
		lemma_eq_sym(temp_55_1, temp_55_0);
	}
	let temp_56_0 = (mul_((mod_((mul_(c, d)), m)), (mul_(a, b))));
	let temp_56_1 = (mul_((mod_((add_((mul_((mul_((mul_(b, a)), (mul_(a, b)))), m)), (mul_(c, d)))), m)), (mul_(a, b))));
	assert(eq_(temp_56_0, temp_56_1)) by {
		lemma_mod_mul_vanish(mul_(c, d), mul_(mul_(b, a), mul_(a, b)), m);
		cong_mul_(mod_(mul_(c, d), m), mul_(a, b), mod_(add_(mul_(mul_(mul_(b, a), mul_(a, b)), m), mul_(c, d)), m), mul_(a, b));
		lemma_eq_ref(mul_(a, b));
	}
	let temp_57_0 = (mul_((mul_(c, (mod_(b, m)))), (mul_(b, a))));
	let temp_57_1 = (mul_((mul_(c, (mod_((add_(b, (mul_((mul_((mul_(a, (mod_(a, m)))), (mul_(c, d)))), m)))), m)))), (mul_(b, a))));
	assert(eq_(temp_57_0, temp_57_1)) by {
		lemma_mod_mul_vanish(b, mul_(mul_(a, mod_(a, m)), mul_(c, d)), m);
		cong_mul_(mul_(c, mod_(b, m)), mul_(b, a), mul_(c, mod_(add_(b, mul_(mul_(mul_(a, mod_(a, m)), mul_(c, d)), m)), m)), mul_(b, a));
		lemma_eq_ref(c);
		cong_mul_(c, mod_(b, m), c, mod_(add_(b, mul_(mul_(mul_(a, mod_(a, m)), mul_(c, d)), m)), m));
		lemma_eq_ref(mul_(b, a));
	}
	let temp_58_0 = (sub_((mod_((mul_(a, b)), m)), (mod_((add_(d, d)), m))));
	let temp_58_1 = (sub_((mod_((mul_(b, a)), m)), (mod_((add_(d, d)), m))));
	assert(eq_(temp_58_0, temp_58_1)) by {
		lemma_mul_comm(a, b);
		cong_sub_(mod_(mul_(a, b), m), mod_(add_(d, d), m), mod_(mul_(b, a), m), mod_(add_(d, d), m));
		lemma_eq_ref(add_(d, d));
		cong_mod_(mul_(a, b), m, mul_(b, a), m);
		cong_mod_(add_(d, d), m, add_(d, d), m);
		lemma_eq_ref(m);
	}
	let temp_59_0 = (mul_((mul_(a, (mod_(b, m)))), (mul_(a, as_elem(72)))));
	let temp_59_1 = (mul_((mul_(a, (mod_((add_((mul_((sub_((sub_(a, a)), (mul_(d, d)))), m)), b)), m)))), (mul_(a, as_elem(72)))));
	assert(eq_(temp_59_0, temp_59_1)) by {
		cong_mul_(a, mod_(b, m), a, mod_(add_(mul_(sub_(sub_(a, a), mul_(d, d)), m), b), m));
		lemma_eq_ref(mul_(a, as_elem(72)));
		lemma_eq_ref(a);
		lemma_mod_mul_vanish(b, sub_(sub_(a, a), mul_(d, d)), m);
		cong_mul_(mul_(a, mod_(b, m)), mul_(a, as_elem(72)), mul_(a, mod_(add_(mul_(sub_(sub_(a, a), mul_(d, d)), m), b), m)), mul_(a, as_elem(72)));
	}
	let temp_60_0 = (add_(c, (mod_((mul_(d, c)), m))));
	let temp_60_1 = (add_(c, (mod_((mul_(c, d)), m))));
	assert(eq_(temp_60_0, temp_60_1)) by {
		cong_add_(c, mod_(mul_(d, c), m), c, mod_(mul_(c, d), m));
		lemma_mul_comm(d, c);
		lemma_eq_ref(c);
		cong_mod_(mul_(d, c), m, mul_(c, d), m);
		lemma_eq_ref(m);
	}
	let temp_61_0 = (mul_((mod_((mul_(b, d)), m)), (mod_((mul_(d, d)), m))));
	let temp_61_1 = (mul_((mod_((sub_((mul_(b, d)), (mul_((mul_((sub_(c, d)), (mul_((mod_(b, m)), b)))), m)))), m)), (mod_((mul_(d, d)), m))));
	assert(eq_(temp_61_0, temp_61_1)) by {
		lemma_mod_mul_vanish(mul_(b, d), mul_(sub_(c, d), mul_(mod_(b, m), b)), m);
		cong_mul_(mod_(mul_(b, d), m), mod_(mul_(d, d), m), mod_(sub_(mul_(b, d), mul_(mul_(sub_(c, d), mul_(mod_(b, m), b)), m)), m), mod_(mul_(d, d), m));
		lemma_eq_ref(mod_(mul_(d, d), m));
	}
	let temp_62_0 = (mul_((mul_(c, b)), (mul_(c, b))));
	let temp_62_1 = (mul_((mul_(c, b)), (mul_(c, b))));
	assert(eq_(temp_62_0, temp_62_1)) by {
		lemma_eq_ref(temp_62_0);
	}
	let temp_63_0 = (mul_((mul_(b, c)), (mul_(as_elem(21), c))));
	let temp_63_1 = (mul_((mul_(as_elem(21), c)), (mul_(b, c))));
	assert(eq_(temp_63_0, temp_63_1)) by {
		lemma_mul_comm(mul_(b, c), mul_(as_elem(21), c));
	}
	let temp_64_0 = (add_((mul_(d, a)), (mul_(a, (mod_(c, m))))));
	let temp_64_1 = (add_((mul_(a, d)), (mul_(a, (mod_(c, m))))));
	assert(eq_(temp_64_0, temp_64_1)) by {
		lemma_mul_comm(d, a);
		cong_add_(mul_(d, a), mul_(a, mod_(c, m)), mul_(a, d), mul_(a, mod_(c, m)));
		lemma_eq_ref(mul_(a, mod_(c, m)));
	}
	let temp_65_0 = (mul_((mul_(d, a)), (mul_(a, a))));
	let temp_65_1 = (mul_((mul_((mul_(d, a)), a)), a));
	assert(eq_(temp_65_0, temp_65_1)) by {
		lemma_mul_assoc(mul_(d, a), a, a);
	}
	let temp_66_0 = (mul_((mul_(d, as_elem(56))), (mul_(a, d))));
	let temp_66_1 = (mul_((mul_(a, d)), (mul_(d, as_elem(56)))));
	assert(eq_(temp_66_0, temp_66_1)) by {
		lemma_mul_comm(mul_(d, as_elem(56)), mul_(a, d));
	}
	let temp_67_0 = (mul_((add_(d, c)), (mul_(a, (mod_(c, m))))));
	let temp_67_1 = (add_((mul_(d, (mul_(a, (mod_(c, m)))))), (mul_(c, (mul_(a, (mod_(c, m))))))));
	assert(eq_(temp_67_0, temp_67_1)) by {
		lemma_mul_dist(d, c, mul_(a, mod_(c, m)));
	}
	let temp_68_0 = (mul_((mul_(as_elem(15), c)), (mod_((mul_(b, d)), m))));
	let temp_68_1 = (mul_(as_elem(15), (mul_(c, (mod_((mul_(b, d)), m))))));
	assert(eq_(temp_68_0, temp_68_1)) by {
		lemma_mul_assoc(as_elem(15), c, mod_(mul_(b, d), m));
		lemma_eq_sym(temp_68_1, temp_68_0);
	}
	let temp_69_0 = (mul_((mul_(d, d)), (mod_((mul_(c, as_elem(70))), m))));
	let temp_69_1 = (mul_((mul_(d, d)), (mod_((mul_(c, as_elem(70))), m))));
	assert(eq_(temp_69_0, temp_69_1)) by {
		lemma_eq_ref(temp_69_0);
	}
	let temp_70_0 = (add_((sub_(b, d)), (mul_(as_elem(75), d))));
	let temp_70_1 = (add_((sub_(b, d)), (mul_(d, as_elem(75)))));
	assert(eq_(temp_70_0, temp_70_1)) by {
		cong_add_(sub_(b, d), mul_(as_elem(75), d), sub_(b, d), mul_(d, as_elem(75)));
		lemma_mul_comm(as_elem(75), d);
		lemma_eq_ref(sub_(b, d));
	}
	let temp_71_0 = (mod_((mul_((mul_(d, as_elem(34))), (mul_(a, c)))), m));
	let temp_71_1 = (mod_((mul_(d, (mul_(as_elem(34), (mul_(a, c)))))), m));
	assert(eq_(temp_71_0, temp_71_1)) by {
		lemma_mul_assoc(d, as_elem(34), mul_(a, c));
		cong_mod_(mul_(mul_(d, as_elem(34)), mul_(a, c)), m, mul_(d, mul_(as_elem(34), mul_(a, c))), m);
		lemma_eq_sym(mul_(d, mul_(as_elem(34), mul_(a, c))), mul_(mul_(d, as_elem(34)), mul_(a, c)));
		lemma_eq_ref(m);
	}
	let temp_72_0 = (mul_((mul_((mod_(b, m)), c)), (mul_(d, d))));
	let temp_72_1 = (mul_((mul_((mod_((add_((mul_((mul_((mul_(d, b)), (mul_(b, b)))), m)), b)), m)), c)), (mul_(d, d))));
	assert(eq_(temp_72_0, temp_72_1)) by {
		lemma_mul_comm(d, d);
		lemma_mod_mul_vanish(b, mul_(mul_(d, b), mul_(b, b)), m);
		cong_mul_(mul_(mod_(b, m), c), mul_(d, d), mul_(mod_(add_(mul_(mul_(mul_(d, b), mul_(b, b)), m), b), m), c), mul_(d, d));
		lemma_eq_ref(c);
		cong_mul_(mod_(b, m), c, mod_(add_(mul_(mul_(mul_(d, b), mul_(b, b)), m), b), m), c);
	}
	let temp_73_0 = (add_((mul_(b, c)), (mod_((add_(a, b)), m))));
	let temp_73_1 = (add_((mod_((add_(a, b)), m)), (mul_(b, c))));
	assert(eq_(temp_73_0, temp_73_1)) by {
		lemma_add_comm(mul_(b, c), mod_(add_(a, b), m));
	}
	let temp_74_0 = (mod_((mul_((mul_(c, c)), (mul_(d, b)))), m));
	let temp_74_1 = (mod_((add_((mul_((mul_(c, c)), (mul_(d, b)))), (mul_((mul_(b, d)), m)))), m));
	assert(eq_(temp_74_0, temp_74_1)) by {
		lemma_mod_mul_vanish(mul_(mul_(c, c), mul_(d, b)), mul_(b, d), m);
	}
	let temp_75_0 = (mod_((mul_((sub_((mod_(b, m)), b)), (add_((mod_(b, m)), d)))), m));
	let temp_75_1 = (mod_((add_((mul_((sub_((mod_(b, m)), b)), (mod_(b, m)))), (mul_((sub_((mod_(b, m)), b)), d)))), m));
	assert(eq_(temp_75_0, temp_75_1)) by {
		lemma_mul_dist(sub_(mod_(b, m), b), mod_(b, m), d);
		cong_mod_(mul_(sub_(mod_(b, m), b), add_(mod_(b, m), d)), m, add_(mul_(sub_(mod_(b, m), b), mod_(b, m)), mul_(sub_(mod_(b, m), b), d)), m);
		lemma_eq_ref(m);
	}
	let temp_76_0 = (mul_((mul_(a, b)), (mul_(d, c))));
	let temp_76_1 = (mul_((mul_((mul_(a, b)), d)), c));
	assert(eq_(temp_76_0, temp_76_1)) by {
		lemma_mul_assoc(mul_(a, b), d, c);
	}
	let temp_77_0 = (mod_((mul_((sub_(a, c)), (mul_(a, a)))), m));
	let temp_77_1 = (mod_((add_((mul_((sub_((mod_((mul_(d, b)), m)), (sub_(c, b)))), m)), (mul_((sub_(a, c)), (mul_(a, a)))))), m));
	assert(eq_(temp_77_0, temp_77_1)) by {
		lemma_mod_mul_vanish(mul_(sub_(a, c), mul_(a, a)), sub_(mod_(mul_(d, b), m), sub_(c, b)), m);
	}
	let temp_78_0 = (mul_((mod_(c, m)), (mul_(d, c))));
	let temp_78_1 = (mul_((mul_((mod_(c, m)), d)), c));
	assert(eq_(temp_78_0, temp_78_1)) by {
		lemma_mul_assoc(mod_(c, m), d, c);
	}
	let temp_79_0 = (mul_((mul_(b, a)), (mod_((sub_(c, b)), m))));
	let temp_79_1 = (mul_((mul_(b, a)), (mod_((sub_((sub_(c, b)), (mul_((add_((mul_(d, b)), (add_(c, a)))), m)))), m))));
	assert(eq_(temp_79_0, temp_79_1)) by {
		lemma_mod_mul_vanish(sub_(c, b), add_(mul_(d, b), add_(c, a)), m);
		cong_mul_(mul_(b, a), mod_(sub_(c, b), m), mul_(b, a), mod_(sub_(sub_(c, b), mul_(add_(mul_(d, b), add_(c, a)), m)), m));
		lemma_eq_ref(mul_(b, a));
	}
	let temp_80_0 = (mul_((mul_(d, (mod_(c, m)))), (mul_((mod_(d, m)), a))));
	let temp_80_1 = (mul_(d, (mul_((mod_(c, m)), (mul_((mod_(d, m)), a))))));
	assert(eq_(temp_80_0, temp_80_1)) by {
		lemma_mul_assoc(d, mod_(c, m), mul_(mod_(d, m), a));
		lemma_eq_sym(temp_80_1, temp_80_0);
	}
	let temp_81_0 = (mul_((mul_(d, b)), (mul_((mod_(a, m)), as_elem(58)))));
	let temp_81_1 = (mul_(d, (mul_(b, (mul_((mod_(a, m)), as_elem(58)))))));
	assert(eq_(temp_81_0, temp_81_1)) by {
		lemma_mul_assoc(d, b, mul_(mod_(a, m), as_elem(58)));
		lemma_eq_sym(temp_81_1, temp_81_0);
	}
	let temp_82_0 = (mod_((mul_((mul_(b, c)), (mul_(a, (mod_(a, m)))))), m));
	let temp_82_1 = (mod_((mul_((mul_(b, c)), (mul_((mod_(a, m)), a)))), m));
	assert(eq_(temp_82_0, temp_82_1)) by {
		lemma_eq_ref(mul_(b, c));
		cong_mul_(mul_(b, c), mul_(a, mod_(a, m)), mul_(b, c), mul_(mod_(a, m), a));
		lemma_eq_ref(m);
		lemma_mul_comm(a, mod_(a, m));
		cong_mod_(mul_(mul_(b, c), mul_(a, mod_(a, m))), m, mul_(mul_(b, c), mul_(mod_(a, m), a)), m);
	}
	let temp_83_0 = (mul_((mul_(a, b)), (mul_(a, d))));
	let temp_83_1 = (mul_((mul_(a, b)), (mul_(d, a))));
	assert(eq_(temp_83_0, temp_83_1)) by {
		cong_mul_(mul_(a, b), mul_(a, d), mul_(a, b), mul_(d, a));
		lemma_mul_comm(a, d);
		lemma_eq_ref(mul_(a, b));
	}
	let temp_84_0 = (mul_((sub_(c, b)), (mul_(a, as_elem(77)))));
	let temp_84_1 = (mul_((mul_((sub_(c, b)), a)), as_elem(77)));
	assert(eq_(temp_84_0, temp_84_1)) by {
		lemma_mul_assoc(sub_(c, b), a, as_elem(77));
	}
	let temp_85_0 = (mod_((mul_((mul_(b, as_elem(85))), (mul_(a, a)))), m));
	let temp_85_1 = (mod_((mul_((mul_(as_elem(85), b)), (mul_(a, a)))), m));
	assert(eq_(temp_85_0, temp_85_1)) by {
		cong_mul_(mul_(b, as_elem(85)), mul_(a, a), mul_(as_elem(85), b), mul_(a, a));
		lemma_eq_ref(m);
		lemma_mul_comm(b, as_elem(85));
		lemma_mul_comm(a, a);
		cong_mod_(mul_(mul_(b, as_elem(85)), mul_(a, a)), m, mul_(mul_(as_elem(85), b), mul_(a, a)), m);
	}
	let temp_86_0 = (add_((mod_((mul_(a, a)), m)), (add_(d, c))));
	let temp_86_1 = (add_((mod_((add_((mul_((mod_((mul_((mod_((mul_(c, (mod_(b, m)))), m)), (mul_(d, a)))), m)), m)), (mul_(a, a)))), m)), (add_(d, c))));
	assert(eq_(temp_86_0, temp_86_1)) by {
		lemma_mod_mul_vanish(mul_(a, a), mod_(mul_(mod_(mul_(c, mod_(b, m)), m), mul_(d, a)), m), m);
		cong_add_(mod_(mul_(a, a), m), add_(d, c), mod_(add_(mul_(mod_(mul_(mod_(mul_(c, mod_(b, m)), m), mul_(d, a)), m), m), mul_(a, a)), m), add_(d, c));
		lemma_eq_ref(add_(d, c));
	}
	let temp_87_0 = (mod_((mul_((mul_(b, as_elem(12))), (mod_((mul_(d, as_elem(95))), m)))), m));
	let temp_87_1 = (mod_((mul_((mul_(b, as_elem(12))), (mod_((mul_(as_elem(95), d)), m)))), m));
	assert(eq_(temp_87_0, temp_87_1)) by {
		lemma_mul_comm(d, as_elem(95));
		cong_mod_(mul_(mul_(b, as_elem(12)), mod_(mul_(d, as_elem(95)), m)), m, mul_(mul_(b, as_elem(12)), mod_(mul_(as_elem(95), d), m)), m);
		lemma_eq_ref(m);
		lemma_eq_ref(mul_(b, as_elem(12)));
		cong_mod_(mul_(d, as_elem(95)), m, mul_(as_elem(95), d), m);
		cong_mul_(mul_(b, as_elem(12)), mod_(mul_(d, as_elem(95)), m), mul_(b, as_elem(12)), mod_(mul_(as_elem(95), d), m));
	}
	let temp_88_0 = (mod_((add_((mul_(b, a)), (mul_((mod_(d, m)), d)))), m));
	let temp_88_1 = (mod_((add_((mod_((mul_(b, a)), m)), (mul_((mod_(d, m)), d)))), m));
	assert(eq_(temp_88_0, temp_88_1)) by {
		lemma_mod_add_noop(mul_(b, a), mul_(mod_(d, m), d), m);
	}
	let temp_89_0 = (mul_((mod_((mul_(c, b)), m)), (mul_(b, d))));
	let temp_89_1 = (mul_((mod_((mul_(b, c)), m)), (mul_(b, d))));
	assert(eq_(temp_89_0, temp_89_1)) by {
		lemma_mul_comm(c, b);
		cong_mul_(mod_(mul_(c, b), m), mul_(b, d), mod_(mul_(b, c), m), mul_(b, d));
		cong_mod_(mul_(c, b), m, mul_(b, c), m);
		lemma_eq_ref(mul_(b, d));
		lemma_eq_ref(m);
	}
	let temp_90_0 = (sub_((mul_(c, a)), (mul_(b, d))));
	let temp_90_1 = (sub_((mul_(c, a)), (mul_(d, b))));
	assert(eq_(temp_90_0, temp_90_1)) by {
		cong_sub_(mul_(c, a), mul_(b, d), mul_(c, a), mul_(d, b));
		lemma_mul_comm(b, d);
		lemma_eq_ref(mul_(c, a));
	}
	let temp_91_0 = (mul_((mul_(b, c)), (mul_(d, c))));
	let temp_91_1 = (mul_((mul_(d, c)), (mul_(b, c))));
	assert(eq_(temp_91_0, temp_91_1)) by {
		lemma_mul_comm(mul_(b, c), mul_(d, c));
	}
	let temp_92_0 = (mul_((mod_((mul_(as_elem(28), b)), m)), (mul_(a, c))));
	let temp_92_1 = (mul_((mod_((mul_(as_elem(28), b)), m)), (mul_(c, a))));
	assert(eq_(temp_92_0, temp_92_1)) by {
		lemma_mul_comm(a, c);
		cong_mul_(mod_(mul_(as_elem(28), b), m), mul_(a, c), mod_(mul_(as_elem(28), b), m), mul_(c, a));
		lemma_eq_ref(mod_(mul_(as_elem(28), b), m));
	}
	let temp_93_0 = (mul_((mul_(c, b)), (add_((mod_(b, m)), a))));
	let temp_93_1 = (mul_((mul_(c, b)), (add_((mod_((sub_(b, (mul_((mul_((mul_(c, d)), (mul_(d, d)))), m)))), m)), a))));
	assert(eq_(temp_93_0, temp_93_1)) by {
		lemma_mod_mul_vanish(b, mul_(mul_(c, d), mul_(d, d)), m);
		cong_mul_(mul_(c, b), add_(mod_(b, m), a), mul_(c, b), add_(mod_(sub_(b, mul_(mul_(mul_(c, d), mul_(d, d)), m)), m), a));
		lemma_eq_ref(mul_(c, b));
		lemma_eq_ref(a);
		cong_add_(mod_(b, m), a, mod_(sub_(b, mul_(mul_(mul_(c, d), mul_(d, d)), m)), m), a);
	}
	let temp_94_0 = (mul_((mul_(a, b)), (mul_(b, (mod_(a, m))))));
	let temp_94_1 = (mul_((mul_(a, b)), (mul_(b, (mod_((add_((mul_((mul_((sub_(b, b)), (sub_(b, d)))), m)), a)), m))))));
	assert(eq_(temp_94_0, temp_94_1)) by {
		lemma_eq_ref(mul_(a, b));
		cong_mul_(b, mod_(a, m), b, mod_(add_(mul_(mul_(sub_(b, b), sub_(b, d)), m), a), m));
		lemma_eq_ref(b);
		lemma_mod_mul_vanish(a, mul_(sub_(b, b), sub_(b, d)), m);
		cong_mul_(mul_(a, b), mul_(b, mod_(a, m)), mul_(a, b), mul_(b, mod_(add_(mul_(mul_(sub_(b, b), sub_(b, d)), m), a), m)));
	}
	let temp_95_0 = (add_((mul_(c, (mod_(c, m)))), (add_(b, c))));
	let temp_95_1 = (add_((mul_((mod_(c, m)), c)), (add_(b, c))));
	assert(eq_(temp_95_0, temp_95_1)) by {
		cong_add_(mul_(c, mod_(c, m)), add_(b, c), mul_(mod_(c, m), c), add_(b, c));
		lemma_mul_comm(c, mod_(c, m));
		lemma_eq_ref(add_(b, c));
	}
	let temp_96_0 = (mul_((mul_(d, d)), (mul_(c, a))));
	let temp_96_1 = (mul_((mul_((mul_(d, d)), c)), a));
	assert(eq_(temp_96_0, temp_96_1)) by {
		lemma_mul_assoc(mul_(d, d), c, a);
	}
	let temp_97_0 = (sub_((sub_(c, b)), (mul_(d, c))));
	let temp_97_1 = (sub_((sub_(c, b)), (mul_(c, d))));
	assert(eq_(temp_97_0, temp_97_1)) by {
		lemma_eq_ref(sub_(c, b));
		cong_sub_(sub_(c, b), mul_(d, c), sub_(c, b), mul_(c, d));
		lemma_mul_comm(d, c);
	}
	let temp_98_0 = (mul_((sub_(c, d)), (mul_(a, c))));
	let temp_98_1 = (sub_((mul_(c, (mul_(a, c)))), (mul_(d, (mul_(a, c))))));
	assert(eq_(temp_98_0, temp_98_1)) by {
		lemma_mul_dist(mul_(a, c), c, d);
	}
	let temp_99_0 = (mod_((mul_((sub_(c, c)), (mul_(c, c)))), m));
	let temp_99_1 = (mod_((add_((mul_((sub_((mul_(a, (mod_(c, m)))), (mul_(d, (mod_(b, m)))))), m)), (mul_((sub_(c, c)), (mul_(c, c)))))), m));
	assert(eq_(temp_99_0, temp_99_1)) by {
		lemma_mod_mul_vanish(mul_(sub_(c, c), mul_(c, c)), sub_(mul_(a, mod_(c, m)), mul_(d, mod_(b, m))), m);
	}
	let temp_100_0 = (mul_((mul_(as_elem(53), d)), (mul_(b, (mod_(b, m))))));
	let temp_100_1 = (mul_(as_elem(53), (mul_(d, (mul_(b, (mod_(b, m))))))));
	assert(eq_(temp_100_0, temp_100_1)) by {
		lemma_mul_assoc(as_elem(53), d, mul_(b, mod_(b, m)));
		lemma_eq_sym(temp_100_1, temp_100_0);
	}
	let temp_101_0 = (add_((add_(d, a)), (mod_((sub_(b, a)), m))));
	let temp_101_1 = (add_((add_(d, a)), (mod_((sub_(b, (mod_(a, m)))), m))));
	assert(eq_(temp_101_0, temp_101_1)) by {
		cong_add_(add_(d, a), mod_(sub_(b, a), m), add_(d, a), mod_(sub_(b, mod_(a, m)), m));
		lemma_mod_sub_noop(b, a, m);
		lemma_eq_ref(add_(d, a));
	}
	let temp_102_0 = (mod_((mul_((mul_(c, c)), (mul_(d, d)))), m));
	let temp_102_1 = (mod_((mul_((mul_(c, c)), (mul_(d, d)))), m));
	assert(eq_(temp_102_0, temp_102_1)) by {
		lemma_eq_ref(temp_102_0);
	}
	let temp_103_0 = (mod_((add_((mul_(d, a)), (mul_(d, c)))), m));
	let temp_103_1 = (mod_((add_((mul_(d, a)), (mul_(c, d)))), m));
	assert(eq_(temp_103_0, temp_103_1)) by {
		lemma_mul_comm(d, c);
		cong_mod_(add_(mul_(d, a), mul_(d, c)), m, add_(mul_(d, a), mul_(c, d)), m);
		lemma_eq_ref(mul_(d, a));
		cong_add_(mul_(d, a), mul_(d, c), mul_(d, a), mul_(c, d));
		lemma_eq_ref(m);
	}
	let temp_104_0 = (mod_((mul_(d, (mul_(b, c)))), m));
	let temp_104_1 = (mod_((mul_(d, (mul_(c, b)))), m));
	assert(eq_(temp_104_0, temp_104_1)) by {
		lemma_mul_comm(b, c);
		cong_mod_(mul_(d, mul_(b, c)), m, mul_(d, mul_(c, b)), m);
		lemma_eq_ref(d);
		cong_mul_(d, mul_(b, c), d, mul_(c, b));
		lemma_eq_ref(m);
	}
	let temp_105_0 = (mul_((add_(b, c)), (mul_(b, b))));
	let temp_105_1 = (mul_((mul_((add_(b, c)), b)), b));
	assert(eq_(temp_105_0, temp_105_1)) by {
		lemma_mul_assoc(add_(b, c), b, b);
	}
	let temp_106_0 = (mod_((sub_((add_(a, b)), (mul_(d, (mod_(a, m)))))), m));
	let temp_106_1 = (mod_((sub_((add_(b, a)), (mul_(d, (mod_(a, m)))))), m));
	assert(eq_(temp_106_0, temp_106_1)) by {
		lemma_add_comm(a, b);
		cong_mod_(sub_(add_(a, b), mul_(d, mod_(a, m))), m, sub_(add_(b, a), mul_(d, mod_(a, m))), m);
		lemma_eq_ref(m);
		cong_sub_(add_(a, b), mul_(d, mod_(a, m)), add_(b, a), mul_(d, mod_(a, m)));
		lemma_eq_ref(mul_(d, mod_(a, m)));
	}
	let temp_107_0 = (mul_((mul_(d, a)), (add_(d, c))));
	let temp_107_1 = (mul_((mul_(a, d)), (add_(d, c))));
	assert(eq_(temp_107_0, temp_107_1)) by {
		cong_mul_(mul_(d, a), add_(d, c), mul_(a, d), add_(d, c));
		lemma_mul_comm(d, a);
		lemma_eq_ref(add_(d, c));
	}
	let temp_108_0 = (mod_((mul_((add_(a, a)), (mul_(c, (mod_(c, m)))))), m));
	let temp_108_1 = (mod_((mul_((add_(a, a)), (mul_(c, (mod_(c, m)))))), m));
	assert(eq_(temp_108_0, temp_108_1)) by {
		lemma_eq_ref(temp_108_0);
	}
	let temp_109_0 = (add_((add_(b, d)), (add_((mod_(d, m)), c))));
	let temp_109_1 = (add_((add_(d, b)), (add_((mod_(d, m)), c))));
	assert(eq_(temp_109_0, temp_109_1)) by {
		lemma_add_comm(b, d);
		cong_add_(add_(b, d), add_(mod_(d, m), c), add_(d, b), add_(mod_(d, m), c));
		lemma_eq_ref(add_(mod_(d, m), c));
	}

}

} // verus!