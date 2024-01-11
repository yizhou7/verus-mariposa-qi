use builtin_macros::*;
// use builtin::*;
mod nl_basics;
use crate::nl_basics::*;
verus! {

pub proof fn free_0(a: Elem, b: Elem, c: Elem, d: Elem, m: Elem)
{
	let temp_0_0 = (mul_((mul_(b, d)), (sub_(c, c))));
	let temp_0_1 = (mul_((sub_(c, c)), (mul_(b, d))));
	assert(eq_(temp_0_0, temp_0_1)) by {
		lemma_mul_comm(mul_(b, d), sub_(c, c));
	}
	let temp_1_0 = (mul_((mul_((mod_(d, m)), c)), (mul_(c, c))));
	let temp_1_1 = (mul_((mul_((mod_((sub_(d, (mul_((mul_((mul_(d, a)), (mul_((mod_(c, m)), (mod_(a, m)))))), m)))), m)), c)), (mul_(c, c))));
	assert(eq_(temp_1_0, temp_1_1)) by {
		lemma_mul_comm(c, c);
		lemma_mod_mul_vanish(d, mul_(mul_(d, a), mul_(mod_(c, m), mod_(a, m))), m);
		cong_mul_(mul_(mod_(d, m), c), mul_(c, c), mul_(mod_(sub_(d, mul_(mul_(mul_(d, a), mul_(mod_(c, m), mod_(a, m))), m)), m), c), mul_(c, c));
		lemma_eq_ref(c);
		cong_mul_(mod_(d, m), c, mod_(sub_(d, mul_(mul_(mul_(d, a), mul_(mod_(c, m), mod_(a, m))), m)), m), c);
	}
	let temp_2_0 = (mod_((mul_((mul_(a, (mod_(d, m)))), (mul_(b, c)))), m));
	let temp_2_1 = (mod_((mul_((mul_(b, c)), (mul_(a, (mod_(d, m)))))), m));
	assert(eq_(temp_2_0, temp_2_1)) by {
		lemma_mul_comm(mul_(a, mod_(d, m)), mul_(b, c));
		cong_mod_(mul_(mul_(a, mod_(d, m)), mul_(b, c)), m, mul_(mul_(b, c), mul_(a, mod_(d, m))), m);
		lemma_eq_ref(m);
	}
	let temp_3_0 = (mul_((mod_((add_(b, a)), m)), (mod_((mul_(as_elem(35), d)), m))));
	let temp_3_1 = (mul_((mod_((mul_(as_elem(35), d)), m)), (mod_((add_(b, a)), m))));
	assert(eq_(temp_3_0, temp_3_1)) by {
		lemma_mul_comm(mod_(add_(b, a), m), mod_(mul_(as_elem(35), d), m));
	}
	let temp_4_0 = (mul_((mul_(b, c)), (mul_(d, c))));
	let temp_4_1 = (mul_((mul_(c, b)), (mul_(d, c))));
	assert(eq_(temp_4_0, temp_4_1)) by {
		cong_mul_(mul_(b, c), mul_(d, c), mul_(c, b), mul_(d, c));
		lemma_mul_comm(b, c);
		lemma_eq_ref(mul_(d, c));
	}
	let temp_5_0 = (mul_((mul_(c, c)), (mul_(c, c))));
	let temp_5_1 = (mul_((mul_((mul_(c, c)), c)), c));
	assert(eq_(temp_5_0, temp_5_1)) by {
		lemma_mul_assoc(mul_(c, c), c, c);
	}
	let temp_6_0 = (mul_((mul_(b, c)), (mod_((mul_(c, a)), m))));
	let temp_6_1 = (mul_((mul_(b, c)), (mod_((mul_(a, c)), m))));
	assert(eq_(temp_6_0, temp_6_1)) by {
		lemma_mul_comm(c, a);
		cong_mul_(mul_(b, c), mod_(mul_(c, a), m), mul_(b, c), mod_(mul_(a, c), m));
		lemma_eq_ref(mul_(b, c));
		cong_mod_(mul_(c, a), m, mul_(a, c), m);
		lemma_eq_ref(m);
	}
	let temp_7_0 = (mul_((add_(a, (mod_(a, m)))), (mul_(b, a))));
	let temp_7_1 = (add_((mul_(a, (mul_(b, a)))), (mul_((mod_(a, m)), (mul_(b, a))))));
	assert(eq_(temp_7_0, temp_7_1)) by {
		lemma_mul_dist(a, mod_(a, m), mul_(b, a));
	}
	let temp_8_0 = (mul_((sub_((mod_(b, m)), c)), (mul_(d, a))));
	let temp_8_1 = (sub_((mul_((mod_(b, m)), (mul_(d, a)))), (mul_(c, (mul_(d, a))))));
	assert(eq_(temp_8_0, temp_8_1)) by {
		lemma_mul_dist(mul_(d, a), mod_(b, m), c);
	}
	let temp_9_0 = (mul_((add_(as_elem(15), d)), (mul_(d, b))));
	let temp_9_1 = (mul_((add_(d, as_elem(15))), (mul_(d, b))));
	assert(eq_(temp_9_0, temp_9_1)) by {
		lemma_add_comm(as_elem(15), d);
		cong_mul_(add_(as_elem(15), d), mul_(d, b), add_(d, as_elem(15)), mul_(d, b));
		lemma_eq_ref(mul_(d, b));
	}
	let temp_10_0 = (mul_((mul_(b, b)), (add_(b, (mod_(c, m))))));
	let temp_10_1 = (add_((mul_((mul_(b, b)), b)), (mul_((mul_(b, b)), (mod_(c, m))))));
	assert(eq_(temp_10_0, temp_10_1)) by {
		lemma_mul_dist(mul_(b, b), b, mod_(c, m));
	}
	let temp_11_0 = (mul_((sub_(d, b)), (mul_(c, b))));
	let temp_11_1 = (mul_((mul_(c, b)), (sub_(d, b))));
	assert(eq_(temp_11_0, temp_11_1)) by {
		lemma_mul_comm(sub_(d, b), mul_(c, b));
	}
	let temp_12_0 = (mul_((mul_(c, c)), (mul_(a, a))));
	let temp_12_1 = (mul_((mul_(c, c)), (mul_(a, a))));
	assert(eq_(temp_12_0, temp_12_1)) by {
		lemma_eq_ref(temp_12_0);
	}
	let temp_13_0 = (mul_((mul_(b, c)), (mul_(b, (mod_(b, m))))));
	let temp_13_1 = (mul_((mul_((mul_(b, c)), b)), (mod_(b, m))));
	assert(eq_(temp_13_0, temp_13_1)) by {
		lemma_mul_assoc(mul_(b, c), b, mod_(b, m));
	}
	let temp_14_0 = (mul_((mul_(c, b)), (mul_(d, d))));
	let temp_14_1 = (mul_((mul_((mul_(c, b)), d)), d));
	assert(eq_(temp_14_0, temp_14_1)) by {
		lemma_mul_assoc(mul_(c, b), d, d);
	}
	let temp_15_0 = (mul_((mul_(b, c)), (mul_(a, d))));
	let temp_15_1 = (mul_((mul_((mul_(b, c)), a)), d));
	assert(eq_(temp_15_0, temp_15_1)) by {
		lemma_mul_assoc(mul_(b, c), a, d);
	}
	let temp_16_0 = (sub_((mul_(c, d)), (add_(c, a))));
	let temp_16_1 = (sub_((mul_(d, c)), (add_(c, a))));
	assert(eq_(temp_16_0, temp_16_1)) by {
		cong_sub_(mul_(c, d), add_(c, a), mul_(d, c), add_(c, a));
		lemma_mul_comm(c, d);
		lemma_eq_ref(add_(c, a));
	}
	let temp_17_0 = (mod_((mul_((mul_(d, a)), (mul_(b, d)))), m));
	let temp_17_1 = (mod_((mul_(d, (mul_(a, (mul_(b, d)))))), m));
	assert(eq_(temp_17_0, temp_17_1)) by {
		lemma_mul_assoc(d, a, mul_(b, d));
		cong_mod_(mul_(mul_(d, a), mul_(b, d)), m, mul_(d, mul_(a, mul_(b, d))), m);
		lemma_eq_sym(mul_(d, mul_(a, mul_(b, d))), mul_(mul_(d, a), mul_(b, d)));
		lemma_eq_ref(m);
	}
	let temp_18_0 = (mul_((mul_(a, c)), (mul_(a, c))));
	let temp_18_1 = (mul_((mul_(a, c)), (mul_(c, a))));
	assert(eq_(temp_18_0, temp_18_1)) by {
		cong_mul_(mul_(a, c), mul_(a, c), mul_(a, c), mul_(c, a));
		lemma_mul_comm(a, c);
		lemma_eq_ref(mul_(a, c));
	}
	let temp_19_0 = (mod_((mul_((add_(as_elem(4), c)), (mul_(a, b)))), m));
	let temp_19_1 = (mod_((mul_((add_(c, as_elem(4))), (mul_(a, b)))), m));
	assert(eq_(temp_19_0, temp_19_1)) by {
		lemma_add_comm(as_elem(4), c);
		cong_mod_(mul_(add_(as_elem(4), c), mul_(a, b)), m, mul_(add_(c, as_elem(4)), mul_(a, b)), m);
		lemma_eq_ref(mul_(a, b));
		cong_mul_(add_(as_elem(4), c), mul_(a, b), add_(c, as_elem(4)), mul_(a, b));
		lemma_eq_ref(m);
	}
	let temp_20_0 = (mod_((mul_((mod_((mul_(a, c)), m)), (sub_(b, a)))), m));
	let temp_20_1 = (mod_((add_((mul_((mul_((mul_(d, (mod_(b, m)))), (mul_(b, d)))), m)), (mul_((mod_((mul_(a, c)), m)), (sub_(b, a)))))), m));
	assert(eq_(temp_20_0, temp_20_1)) by {
		lemma_mod_mul_vanish(mul_(mod_(mul_(a, c), m), sub_(b, a)), mul_(mul_(d, mod_(b, m)), mul_(b, d)), m);
	}
	let temp_21_0 = (mul_((sub_(a, a)), (sub_(c, b))));
	let temp_21_1 = (mul_((sub_(c, b)), (sub_(a, a))));
	assert(eq_(temp_21_0, temp_21_1)) by {
		lemma_mul_comm(sub_(a, a), sub_(c, b));
	}
	let temp_22_0 = (mul_((mul_(b, a)), (mod_((mul_(c, a)), m))));
	let temp_22_1 = (mul_((mul_(b, a)), (mod_((mul_(a, c)), m))));
	assert(eq_(temp_22_0, temp_22_1)) by {
		lemma_mul_comm(c, a);
		cong_mul_(mul_(b, a), mod_(mul_(c, a), m), mul_(b, a), mod_(mul_(a, c), m));
		lemma_eq_ref(mul_(b, a));
		cong_mod_(mul_(c, a), m, mul_(a, c), m);
		lemma_eq_ref(m);
	}
	let temp_23_0 = (mul_((mul_(d, as_elem(100))), (mul_(c, d))));
	let temp_23_1 = (mul_((mul_((mul_(d, as_elem(100))), c)), d));
	assert(eq_(temp_23_0, temp_23_1)) by {
		lemma_mul_assoc(mul_(d, as_elem(100)), c, d);
	}
	let temp_24_0 = (sub_((mul_(a, a)), (mul_((mod_(a, m)), d))));
	let temp_24_1 = (sub_((mul_(a, a)), (mul_((mod_((add_((mul_((add_((mul_(c, c)), (mul_(a, as_elem(25))))), m)), a)), m)), d))));
	assert(eq_(temp_24_0, temp_24_1)) by {
		lemma_mul_comm(a, a);
		lemma_mod_mul_vanish(a, add_(mul_(c, c), mul_(a, as_elem(25))), m);
		cong_sub_(mul_(a, a), mul_(mod_(a, m), d), mul_(a, a), mul_(mod_(add_(mul_(add_(mul_(c, c), mul_(a, as_elem(25))), m), a), m), d));
		lemma_eq_ref(d);
		cong_mul_(mod_(a, m), d, mod_(add_(mul_(add_(mul_(c, c), mul_(a, as_elem(25))), m), a), m), d);
	}
	let temp_25_0 = (mod_((sub_((mul_((mod_(b, m)), (mod_(c, m)))), (sub_(d, c)))), m));
	let temp_25_1 = (mod_((sub_((mul_((mod_(b, m)), (mod_((sub_(c, (mul_((mul_((mul_(c, b)), (mul_(c, as_elem(66))))), m)))), m)))), (sub_(d, c)))), m));
	assert(eq_(temp_25_0, temp_25_1));
	let temp_26_0 = (mul_((sub_(a, b)), (add_(d, d))));
	let temp_26_1 = (sub_((mul_(a, (add_(d, d)))), (mul_(b, (add_(d, d))))));
	assert(eq_(temp_26_0, temp_26_1)) by {
		lemma_mul_dist(add_(d, d), a, b);
	}
	let temp_27_0 = (mul_((mod_((mul_(c, a)), m)), (mul_(c, a))));
	let temp_27_1 = (mul_((mul_(c, a)), (mod_((mul_(c, a)), m))));
	assert(eq_(temp_27_0, temp_27_1)) by {
		lemma_mul_comm(mod_(mul_(c, a), m), mul_(c, a));
	}
	let temp_28_0 = (mul_((mul_(b, (mod_(d, m)))), (add_(d, c))));
	let temp_28_1 = (mul_(b, (mul_((mod_(d, m)), (add_(d, c))))));
	assert(eq_(temp_28_0, temp_28_1)) by {
		lemma_mul_assoc(b, mod_(d, m), add_(d, c));
		lemma_eq_sym(temp_28_1, temp_28_0);
	}
	let temp_29_0 = (mul_((mul_(b, (mod_(d, m)))), (mul_(d, (mod_(b, m))))));
	let temp_29_1 = (mul_((mul_((mod_(d, m)), b)), (mul_(d, (mod_(b, m))))));
	assert(eq_(temp_29_0, temp_29_1)) by {
		lemma_mul_comm(b, mod_(d, m));
		cong_mul_(mul_(b, mod_(d, m)), mul_(d, mod_(b, m)), mul_(mod_(d, m), b), mul_(d, mod_(b, m)));
		lemma_eq_ref(mul_(d, mod_(b, m)));
	}
	let temp_30_0 = (add_((mul_(d, as_elem(26))), (mul_(d, a))));
	let temp_30_1 = (add_((mul_(as_elem(26), d)), (mul_(d, a))));
	assert(eq_(temp_30_0, temp_30_1)) by {
		cong_add_(mul_(d, as_elem(26)), mul_(d, a), mul_(as_elem(26), d), mul_(d, a));
		lemma_mul_comm(d, as_elem(26));
		lemma_eq_ref(mul_(d, a));
	}
	let temp_31_0 = (mul_((mul_(d, d)), (mul_(b, c))));
	let temp_31_1 = (mul_((mul_((mul_(d, d)), b)), c));
	assert(eq_(temp_31_0, temp_31_1)) by {
		lemma_mul_assoc(mul_(d, d), b, c);
	}
	let temp_32_0 = (mul_((mod_((mul_(a, d)), m)), (mul_(c, as_elem(14)))));
	let temp_32_1 = (mul_((mod_((add_((mul_(a, d)), (mul_((mod_((sub_((mul_(a, b)), (mul_(c, (mod_(b, m)))))), m)), m)))), m)), (mul_(c, as_elem(14)))));
	assert(eq_(temp_32_0, temp_32_1)) by {
		lemma_mod_mul_vanish(mul_(a, d), mod_(sub_(mul_(a, b), mul_(c, mod_(b, m))), m), m);
		cong_mul_(mod_(mul_(a, d), m), mul_(c, as_elem(14)), mod_(add_(mul_(a, d), mul_(mod_(sub_(mul_(a, b), mul_(c, mod_(b, m))), m), m)), m), mul_(c, as_elem(14)));
		lemma_eq_ref(mul_(c, as_elem(14)));
	}
	let temp_33_0 = (mod_((mul_((add_(a, a)), (mod_((mul_(d, c)), m)))), m));
	let temp_33_1 = (mod_((mul_((add_(a, a)), (mod_((mul_(c, d)), m)))), m));
	assert(eq_(temp_33_0, temp_33_1)) by {
		lemma_mul_comm(d, c);
		lemma_add_comm(a, a);
		cong_mod_(mul_(add_(a, a), mod_(mul_(d, c), m)), m, mul_(add_(a, a), mod_(mul_(c, d), m)), m);
		cong_mul_(add_(a, a), mod_(mul_(d, c), m), add_(a, a), mod_(mul_(c, d), m));
		lemma_eq_ref(m);
		cong_mod_(mul_(d, c), m, mul_(c, d), m);
	}
	let temp_34_0 = (add_((sub_(b, (mod_(b, m)))), (mul_(a, b))));
	let temp_34_1 = (add_((mul_(a, b)), (sub_(b, (mod_(b, m))))));
	assert(eq_(temp_34_0, temp_34_1)) by {
		lemma_add_comm(sub_(b, mod_(b, m)), mul_(a, b));
	}
	let temp_35_0 = (mul_((add_(a, c)), (mul_(a, b))));
	let temp_35_1 = (mul_((add_(a, c)), (mul_(b, a))));
	assert(eq_(temp_35_0, temp_35_1)) by {
		cong_mul_(add_(a, c), mul_(a, b), add_(a, c), mul_(b, a));
		lemma_mul_comm(a, b);
		lemma_eq_ref(add_(a, c));
	}
	let temp_36_0 = (mul_((mul_(b, c)), (mul_(a, c))));
	let temp_36_1 = (mul_(b, (mul_(c, (mul_(a, c))))));
	assert(eq_(temp_36_0, temp_36_1)) by {
		lemma_eq_sym(temp_36_1, temp_36_0);
		lemma_mul_assoc(b, c, mul_(a, c));
	}
	let temp_37_0 = (mul_((mul_(c, (mod_(a, m)))), (mul_(c, (mod_(c, m))))));
	let temp_37_1 = (mul_(c, (mul_((mod_(a, m)), (mul_(c, (mod_(c, m))))))));
	assert(eq_(temp_37_0, temp_37_1)) by {
		lemma_mul_assoc(c, mod_(a, m), mul_(c, mod_(c, m)));
		lemma_eq_sym(temp_37_1, temp_37_0);
	}
	let temp_38_0 = (add_((mul_(b, d)), (mul_(a, b))));
	let temp_38_1 = (add_((mul_(a, b)), (mul_(b, d))));
	assert(eq_(temp_38_0, temp_38_1)) by {
		lemma_add_comm(mul_(b, d), mul_(a, b));
	}
	let temp_39_0 = (mul_((mul_(a, as_elem(46))), (mul_(c, a))));
	let temp_39_1 = (mul_(a, (mul_(as_elem(46), (mul_(c, a))))));
	assert(eq_(temp_39_0, temp_39_1)) by {
		lemma_eq_sym(temp_39_1, temp_39_0);
		lemma_mul_assoc(a, as_elem(46), mul_(c, a));
	}
	let temp_40_0 = (mul_((mul_(b, b)), (mul_(c, a))));
	let temp_40_1 = (mul_((mul_(b, b)), (mul_(a, c))));
	assert(eq_(temp_40_0, temp_40_1)) by {
		cong_mul_(mul_(b, b), mul_(c, a), mul_(b, b), mul_(a, c));
		lemma_mul_comm(b, b);
		lemma_mul_comm(c, a);
	}
	let temp_41_0 = (mul_((mul_(a, d)), (mul_(a, a))));
	let temp_41_1 = (mul_((mul_(a, a)), (mul_(a, d))));
	assert(eq_(temp_41_0, temp_41_1)) by {
		lemma_mul_comm(mul_(a, d), mul_(a, a));
	}
	let temp_42_0 = (add_((sub_(d, d)), (mul_(a, b))));
	let temp_42_1 = (add_((mul_(a, b)), (sub_(d, d))));
	assert(eq_(temp_42_0, temp_42_1)) by {
		lemma_add_comm(sub_(d, d), mul_(a, b));
	}
	let temp_43_0 = (mod_((add_((mod_((mul_(c, b)), m)), (add_(b, a)))), m));
	let temp_43_1 = (mod_((add_((mod_((mul_(c, b)), m)), (add_(a, b)))), m));
	assert(eq_(temp_43_0, temp_43_1)) by {
		lemma_add_comm(b, a);
		cong_mod_(add_(mod_(mul_(c, b), m), add_(b, a)), m, add_(mod_(mul_(c, b), m), add_(a, b)), m);
		lemma_eq_ref(m);
		cong_add_(mod_(mul_(c, b), m), add_(b, a), mod_(mul_(c, b), m), add_(a, b));
		lemma_eq_ref(mod_(mul_(c, b), m));
	}
	let temp_44_0 = (mul_((mul_(d, d)), (mul_(d, a))));
	let temp_44_1 = (mul_(d, (mul_(d, (mul_(d, a))))));
	assert(eq_(temp_44_0, temp_44_1)) by {
		lemma_eq_sym(temp_44_1, temp_44_0);
		lemma_mul_assoc(d, d, mul_(d, a));
	}
	let temp_45_0 = (mod_((mul_((mul_(a, b)), (mul_(d, a)))), m));
	let temp_45_1 = (mod_((mul_(a, (mul_(b, (mul_(d, a)))))), m));
	assert(eq_(temp_45_0, temp_45_1)) by {
		lemma_mul_assoc(a, b, mul_(d, a));
		cong_mod_(mul_(mul_(a, b), mul_(d, a)), m, mul_(a, mul_(b, mul_(d, a))), m);
		lemma_eq_sym(mul_(a, mul_(b, mul_(d, a))), mul_(mul_(a, b), mul_(d, a)));
		lemma_eq_ref(m);
	}
	let temp_46_0 = (add_((mul_(d, a)), (mul_((mod_(c, m)), b))));
	let temp_46_1 = (add_((mul_(d, a)), (mul_(b, (mod_(c, m))))));
	assert(eq_(temp_46_0, temp_46_1)) by {
		lemma_mul_comm(mod_(c, m), b);
		cong_add_(mul_(d, a), mul_(mod_(c, m), b), mul_(d, a), mul_(b, mod_(c, m)));
		lemma_eq_ref(mul_(d, a));
	}
	let temp_47_0 = (add_((mul_(b, d)), (mul_(d, a))));
	let temp_47_1 = (add_((mul_(b, d)), (mul_(a, d))));
	assert(eq_(temp_47_0, temp_47_1)) by {
		cong_add_(mul_(b, d), mul_(d, a), mul_(b, d), mul_(a, d));
		lemma_mul_comm(d, a);
		lemma_eq_ref(mul_(b, d));
	}
	let temp_48_0 = (mul_((mul_(b, (mod_(a, m)))), (mul_(c, b))));
	let temp_48_1 = (mul_((mul_((mul_(b, (mod_(a, m)))), c)), b));
	assert(eq_(temp_48_0, temp_48_1)) by {
		lemma_mul_assoc(mul_(b, mod_(a, m)), c, b);
	}
	let temp_49_0 = (mul_((mul_(b, d)), (mul_(d, d))));
	let temp_49_1 = (mul_((mul_(d, d)), (mul_(b, d))));
	assert(eq_(temp_49_0, temp_49_1)) by {
		lemma_mul_comm(mul_(b, d), mul_(d, d));
	}
	let temp_50_0 = (mul_((mod_((mul_(b, a)), m)), (mul_(b, b))));
	let temp_50_1 = (mul_((mul_((mod_((mul_(b, a)), m)), b)), b));
	assert(eq_(temp_50_0, temp_50_1)) by {
		lemma_mul_assoc(mod_(mul_(b, a), m), b, b);
	}
	let temp_51_0 = (mul_((mul_(c, d)), (mul_(c, as_elem(81)))));
	let temp_51_1 = (mul_((mul_(c, as_elem(81))), (mul_(c, d))));
	assert(eq_(temp_51_0, temp_51_1)) by {
		lemma_mul_comm(mul_(c, d), mul_(c, as_elem(81)));
	}
	let temp_52_0 = (mul_((mul_(a, c)), (mul_(a, c))));
	let temp_52_1 = (mul_((mul_(a, c)), (mul_(c, a))));
	assert(eq_(temp_52_0, temp_52_1)) by {
		cong_mul_(mul_(a, c), mul_(a, c), mul_(a, c), mul_(c, a));
		lemma_mul_comm(a, c);
		lemma_eq_ref(mul_(a, c));
	}
	let temp_53_0 = (mul_((mul_(b, a)), (mul_(as_elem(51), (mod_(a, m))))));
	let temp_53_1 = (mul_((mul_((mul_(b, a)), as_elem(51))), (mod_(a, m))));
	assert(eq_(temp_53_0, temp_53_1)) by {
		lemma_mul_assoc(mul_(b, a), as_elem(51), mod_(a, m));
	}
	let temp_54_0 = (add_((mul_((mod_(a, m)), b)), (mod_((mul_(c, b)), m))));
	let temp_54_1 = (add_((mul_((mod_(a, m)), b)), (mod_((add_((mul_((mul_(a, (mul_(b, c)))), m)), (mul_(c, b)))), m))));
	assert(eq_(temp_54_0, temp_54_1)) by {
		lemma_mod_mul_vanish(mul_(c, b), mul_(a, mul_(b, c)), m);
		cong_add_(mul_(mod_(a, m), b), mod_(mul_(c, b), m), mul_(mod_(a, m), b), mod_(add_(mul_(mul_(a, mul_(b, c)), m), mul_(c, b)), m));
		lemma_eq_ref(mul_(mod_(a, m), b));
	}
	let temp_55_0 = (mul_((sub_(c, c)), (add_((mod_(a, m)), c))));
	let temp_55_1 = (mul_((add_((mod_(a, m)), c)), (sub_(c, c))));
	assert(eq_(temp_55_0, temp_55_1)) by {
		lemma_mul_comm(sub_(c, c), add_(mod_(a, m), c));
	}
	let temp_56_0 = (mul_((mod_((mul_(a, b)), m)), (mul_(a, b))));
	let temp_56_1 = (mul_((mul_((mod_((mul_(a, b)), m)), a)), b));
	assert(eq_(temp_56_0, temp_56_1)) by {
		lemma_mul_assoc(mod_(mul_(a, b), m), a, b);
	}
	let temp_57_0 = (mul_((mul_(c, c)), (mul_(b, d))));
	let temp_57_1 = (mul_((mul_(b, d)), (mul_(c, c))));
	assert(eq_(temp_57_0, temp_57_1)) by {
		lemma_mul_comm(mul_(c, c), mul_(b, d));
	}
	let temp_58_0 = (add_((sub_((mod_(b, m)), d)), (mul_(d, d))));
	let temp_58_1 = (add_((sub_((mod_(b, m)), d)), (mul_(d, d))));
	assert(eq_(temp_58_0, temp_58_1)) by {
		lemma_eq_ref(temp_58_0);
	}
	let temp_59_0 = (mul_((mul_(b, d)), (mod_((mul_(c, c)), m))));
	let temp_59_1 = (mul_((mod_((mul_(c, c)), m)), (mul_(b, d))));
	assert(eq_(temp_59_0, temp_59_1)) by {
		lemma_mul_comm(mul_(b, d), mod_(mul_(c, c), m));
	}
	let temp_60_0 = (mul_((mul_(b, a)), (mul_(b, c))));
	let temp_60_1 = (mul_((mul_(b, a)), (mul_(c, b))));
	assert(eq_(temp_60_0, temp_60_1)) by {
		cong_mul_(mul_(b, a), mul_(b, c), mul_(b, a), mul_(c, b));
		lemma_mul_comm(b, c);
		lemma_eq_ref(mul_(b, a));
	}
	let temp_61_0 = (mul_((mul_(c, a)), (mul_(b, c))));
	let temp_61_1 = (mul_((mul_(b, c)), (mul_(c, a))));
	assert(eq_(temp_61_0, temp_61_1)) by {
		lemma_mul_comm(mul_(c, a), mul_(b, c));
	}
	let temp_62_0 = (mul_((mul_(d, d)), (mul_(a, a))));
	let temp_62_1 = (mul_((mul_(a, a)), (mul_(d, d))));
	assert(eq_(temp_62_0, temp_62_1)) by {
		lemma_mul_comm(mul_(d, d), mul_(a, a));
	}
	let temp_63_0 = (mod_((sub_((mul_(c, c)), (mul_(c, b)))), m));
	let temp_63_1 = (mod_((sub_((mul_(c, c)), (mul_(b, c)))), m));
	assert(eq_(temp_63_0, temp_63_1)) by {
		lemma_eq_ref(m);
		lemma_mul_comm(c, c);
		lemma_mul_comm(c, b);
		cong_mod_(sub_(mul_(c, c), mul_(c, b)), m, sub_(mul_(c, c), mul_(b, c)), m);
		cong_sub_(mul_(c, c), mul_(c, b), mul_(c, c), mul_(b, c));
	}
	let temp_64_0 = (mul_((mul_(b, a)), (mul_(c, d))));
	let temp_64_1 = (mul_((mul_(a, b)), (mul_(c, d))));
	assert(eq_(temp_64_0, temp_64_1)) by {
		cong_mul_(mul_(b, a), mul_(c, d), mul_(a, b), mul_(c, d));
		lemma_mul_comm(b, a);
		lemma_eq_ref(mul_(c, d));
	}
	let temp_65_0 = (mul_((mul_(c, d)), (mul_(d, c))));
	let temp_65_1 = (mul_(c, (mul_(d, (mul_(d, c))))));
	assert(eq_(temp_65_0, temp_65_1)) by {
		lemma_eq_sym(temp_65_1, temp_65_0);
		lemma_mul_assoc(c, d, mul_(d, c));
	}
	let temp_66_0 = (mul_((mul_(b, (mod_(c, m)))), (mul_(c, c))));
	let temp_66_1 = (mul_((mul_(b, (mod_(c, m)))), (mul_(c, c))));
	assert(eq_(temp_66_0, temp_66_1)) by {
		lemma_eq_ref(temp_66_0);
	}
	let temp_67_0 = (sub_(d, (mul_(a, c))));
	let temp_67_1 = (sub_(d, (mul_(c, a))));
	assert(eq_(temp_67_0, temp_67_1)) by {
		cong_sub_(d, mul_(a, c), d, mul_(c, a));
		lemma_mul_comm(a, c);
		lemma_eq_ref(d);
	}
	let temp_68_0 = (add_((mul_(c, b)), (sub_(d, d))));
	let temp_68_1 = (add_((mul_(b, c)), (sub_(d, d))));
	assert(eq_(temp_68_0, temp_68_1)) by {
		cong_add_(mul_(c, b), sub_(d, d), mul_(b, c), sub_(d, d));
		lemma_mul_comm(c, b);
		lemma_eq_ref(sub_(d, d));
	}
	let temp_69_0 = (mul_((sub_(c, c)), (mod_((mul_(b, a)), m))));
	let temp_69_1 = (mul_((mod_((mul_(b, a)), m)), (sub_(c, c))));
	assert(eq_(temp_69_0, temp_69_1)) by {
		lemma_mul_comm(sub_(c, c), mod_(mul_(b, a), m));
	}
	let temp_70_0 = (mul_((mod_((mul_(a, b)), m)), (mul_(d, (mod_(d, m))))));
	let temp_70_1 = (mul_((mod_((mul_(a, b)), m)), (mul_(d, (mod_((add_((mul_((mul_((mul_(c, a)), (mul_(b, c)))), m)), d)), m))))));
	assert(eq_(temp_70_0, temp_70_1)) by {
		lemma_mod_mul_vanish(d, mul_(mul_(c, a), mul_(b, c)), m);
		cong_mul_(mod_(mul_(a, b), m), mul_(d, mod_(d, m)), mod_(mul_(a, b), m), mul_(d, mod_(add_(mul_(mul_(mul_(c, a), mul_(b, c)), m), d), m)));
		lemma_eq_ref(mod_(mul_(a, b), m));
		cong_mul_(d, mod_(d, m), d, mod_(add_(mul_(mul_(mul_(c, a), mul_(b, c)), m), d), m));
		lemma_eq_ref(d);
	}
	let temp_71_0 = (mul_((mul_(d, as_elem(68))), (mul_(a, a))));
	let temp_71_1 = (mul_(d, (mul_(as_elem(68), (mul_(a, a))))));
	assert(eq_(temp_71_0, temp_71_1)) by {
		lemma_eq_sym(temp_71_1, temp_71_0);
		lemma_mul_assoc(d, as_elem(68), mul_(a, a));
	}
	let temp_72_0 = (mul_((sub_((mod_(a, m)), d)), (mul_(b, d))));
	let temp_72_1 = (mul_((mul_(b, d)), (sub_((mod_(a, m)), d))));
	assert(eq_(temp_72_0, temp_72_1)) by {
		lemma_mul_comm(sub_(mod_(a, m), d), mul_(b, d));
	}
	let temp_73_0 = (mul_((mul_(d, d)), (mul_(c, d))));
	let temp_73_1 = (mul_((mul_(d, d)), (mul_(c, d))));
	assert(eq_(temp_73_0, temp_73_1)) by {
		lemma_eq_ref(temp_73_0);
	}
	let temp_74_0 = (add_((mul_(b, b)), (mul_(b, b))));
	let temp_74_1 = (add_((mul_(b, b)), (mul_(b, b))));
	assert(eq_(temp_74_0, temp_74_1)) by {
		lemma_eq_ref(temp_74_0);
	}
	let temp_75_0 = (mul_((mul_(d, a)), (mul_(d, b))));
	let temp_75_1 = (mul_((mul_((mul_(d, a)), d)), b));
	assert(eq_(temp_75_0, temp_75_1)) by {
		lemma_mul_assoc(mul_(d, a), d, b);
	}
	let temp_76_0 = (mul_((mul_(a, c)), (mul_(as_elem(62), d))));
	let temp_76_1 = (mul_((mul_(as_elem(62), d)), (mul_(a, c))));
	assert(eq_(temp_76_0, temp_76_1)) by {
		lemma_mul_comm(mul_(a, c), mul_(as_elem(62), d));
	}
	let temp_77_0 = (mul_((mul_(b, c)), (mul_(b, c))));
	let temp_77_1 = (mul_((mul_(b, c)), (mul_(c, b))));
	assert(eq_(temp_77_0, temp_77_1)) by {
		cong_mul_(mul_(b, c), mul_(b, c), mul_(b, c), mul_(c, b));
		lemma_mul_comm(b, c);
		lemma_eq_ref(mul_(b, c));
	}
	let temp_78_0 = (mod_((mul_((mul_(c, d)), (mul_(c, as_elem(70))))), m));
	let temp_78_1 = (mod_((sub_((mul_((mul_(c, d)), (mul_(c, as_elem(70))))), (mul_((sub_((sub_(b, c)), (mul_(a, (mod_(a, m)))))), m)))), m));
	assert(eq_(temp_78_0, temp_78_1)) by {
		lemma_mod_mul_vanish(mul_(mul_(c, d), mul_(c, as_elem(70))), sub_(sub_(b, c), mul_(a, mod_(a, m))), m);
	}
	let temp_79_0 = (mul_((mul_(b, c)), (mul_(d, b))));
	let temp_79_1 = (mul_((mul_(d, b)), (mul_(b, c))));
	assert(eq_(temp_79_0, temp_79_1)) by {
		lemma_mul_comm(mul_(b, c), mul_(d, b));
	}
	let temp_80_0 = (mul_((sub_(b, c)), (mod_((mul_(c, (mod_(a, m)))), m))));
	let temp_80_1 = (mul_((sub_(b, c)), (mod_((mod_((mul_(a, c)), m)), m))));
	assert(eq_(temp_80_0, temp_80_1)) by {
		lemma_mod_mul_noop(a, c, m);
		cong_mul_(sub_(b, c), mod_(mul_(c, mod_(a, m)), m), sub_(b, c), mod_(mod_(mul_(a, c), m), m));
		lemma_eq_sym(mod_(mod_(mul_(a, c), m), m), mod_(mul_(c, mod_(a, m)), m));
		lemma_eq_ref(sub_(b, c));
	}
	let temp_81_0 = (mul_(d, (mul_(a, d))));
	let temp_81_1 = (mul_((mul_(a, d)), d));
	assert(eq_(temp_81_0, temp_81_1)) by {
		lemma_mul_comm(d, mul_(a, d));
	}
	let temp_82_0 = (mul_((mul_(c, c)), (mul_(as_elem(26), c))));
	let temp_82_1 = (mul_(c, (mul_(c, (mul_(as_elem(26), c))))));
	assert(eq_(temp_82_0, temp_82_1)) by {
		lemma_eq_sym(temp_82_1, temp_82_0);
		lemma_mul_assoc(c, c, mul_(as_elem(26), c));
	}
	let temp_83_0 = (mul_((mod_((mul_(d, c)), m)), (add_(d, a))));
	let temp_83_1 = (mul_((add_(d, a)), (mod_((mul_(d, c)), m))));
	assert(eq_(temp_83_0, temp_83_1)) by {
		lemma_mul_comm(mod_(mul_(d, c), m), add_(d, a));
	}
	let temp_84_0 = (sub_((mul_(b, b)), (mod_((mul_(a, b)), m))));
	let temp_84_1 = (sub_((mul_(b, b)), (mod_((add_((mul_((mul_((mul_(d, a)), (mod_((mul_(d, d)), m)))), m)), (mul_(a, b)))), m))));
	assert(eq_(temp_84_0, temp_84_1)) by {
		lemma_mul_comm(b, b);
		lemma_mod_mul_vanish(mul_(a, b), mul_(mul_(d, a), mod_(mul_(d, d), m)), m);
		cong_sub_(mul_(b, b), mod_(mul_(a, b), m), mul_(b, b), mod_(add_(mul_(mul_(mul_(d, a), mod_(mul_(d, d), m)), m), mul_(a, b)), m));
	}
	let temp_85_0 = (mul_((mod_((mul_(d, c)), m)), (add_(as_elem(33), b))));
	let temp_85_1 = (add_((mul_((mod_((mul_(d, c)), m)), as_elem(33))), (mul_((mod_((mul_(d, c)), m)), b))));
	assert(eq_(temp_85_0, temp_85_1)) by {
		lemma_mul_dist(mod_(mul_(d, c), m), as_elem(33), b);
	}
	let temp_86_0 = (mul_((mul_(c, c)), (mul_(a, b))));
	let temp_86_1 = (mul_((mul_((mul_(c, c)), a)), b));
	assert(eq_(temp_86_0, temp_86_1)) by {
		lemma_mul_assoc(mul_(c, c), a, b);
	}
	let temp_87_0 = (mul_((mul_(a, b)), (mul_(d, c))));
	let temp_87_1 = (mul_((mul_(b, a)), (mul_(d, c))));
	assert(eq_(temp_87_0, temp_87_1)) by {
		cong_mul_(mul_(a, b), mul_(d, c), mul_(b, a), mul_(d, c));
		lemma_mul_comm(a, b);
		lemma_eq_ref(mul_(d, c));
	}
	let temp_88_0 = (add_((mul_(a, (mod_(b, m)))), (sub_(c, c))));
	let temp_88_1 = (add_((sub_(c, c)), (mul_(a, (mod_(b, m))))));
	assert(eq_(temp_88_0, temp_88_1)) by {
		lemma_add_comm(mul_(a, mod_(b, m)), sub_(c, c));
	}
	let temp_89_0 = (mul_((sub_(c, d)), (sub_(d, a))));
	let temp_89_1 = (mul_((sub_(d, a)), (sub_(c, d))));
	assert(eq_(temp_89_0, temp_89_1)) by {
		lemma_mul_comm(sub_(c, d), sub_(d, a));
	}
	let temp_90_0 = (mul_((mod_((mul_(d, c)), m)), (sub_(d, a))));
	let temp_90_1 = (mul_((mod_((mul_(c, d)), m)), (sub_(d, a))));
	assert(eq_(temp_90_0, temp_90_1)) by {
		lemma_mul_comm(d, c);
		cong_mul_(mod_(mul_(d, c), m), sub_(d, a), mod_(mul_(c, d), m), sub_(d, a));
		cong_mod_(mul_(d, c), m, mul_(c, d), m);
		lemma_eq_ref(sub_(d, a));
		lemma_eq_ref(m);
	}
	let temp_91_0 = (mul_((mod_((mul_(c, b)), m)), (add_(b, (mod_(a, m))))));
	let temp_91_1 = (add_((mul_((mod_((mul_(c, b)), m)), b)), (mul_((mod_((mul_(c, b)), m)), (mod_(a, m))))));
	assert(eq_(temp_91_0, temp_91_1)) by {
		lemma_mul_dist(mod_(mul_(c, b), m), b, mod_(a, m));
	}
	let temp_92_0 = (mul_((mul_(c, (mod_(a, m)))), (mul_(a, c))));
	let temp_92_1 = (mul_((mul_((mod_(a, m)), c)), (mul_(a, c))));
	assert(eq_(temp_92_0, temp_92_1)) by {
		cong_mul_(mul_(c, mod_(a, m)), mul_(a, c), mul_(mod_(a, m), c), mul_(a, c));
		lemma_mul_comm(c, mod_(a, m));
		lemma_eq_ref(mul_(a, c));
	}
	let temp_93_0 = (add_((mul_(b, (mod_(b, m)))), d));
	let temp_93_1 = (add_((mul_(b, (mod_((sub_(b, (mul_((mul_((mul_(b, a)), (mul_(c, b)))), m)))), m)))), d));
	assert(eq_(temp_93_0, temp_93_1)) by {
		lemma_mod_mul_vanish(b, mul_(mul_(b, a), mul_(c, b)), m);
		cong_add_(mul_(b, mod_(b, m)), d, mul_(b, mod_(sub_(b, mul_(mul_(mul_(b, a), mul_(c, b)), m)), m)), d);
		lemma_eq_ref(b);
		cong_mul_(b, mod_(b, m), b, mod_(sub_(b, mul_(mul_(mul_(b, a), mul_(c, b)), m)), m));
		lemma_eq_ref(d);
	}
	let temp_94_0 = (mod_((mul_((mul_((mod_(c, m)), a)), (mod_((mul_(a, a)), m)))), m));
	let temp_94_1 = (mod_((mul_((mul_((mod_(c, m)), a)), (mod_((mul_(a, a)), m)))), m));
	assert(eq_(temp_94_0, temp_94_1)) by {
		lemma_eq_ref(temp_94_0);
	}
	let temp_95_0 = (mul_((mul_(a, as_elem(7))), (add_(a, b))));
	let temp_95_1 = (mul_(a, (mul_(as_elem(7), (add_(a, b))))));
	assert(eq_(temp_95_0, temp_95_1)) by {
		lemma_eq_sym(temp_95_1, temp_95_0);
		lemma_mul_assoc(a, as_elem(7), add_(a, b));
	}
	let temp_96_0 = (mod_((mul_((mul_(c, as_elem(82))), (mul_(b, a)))), m));
	let temp_96_1 = (mod_((mul_((mul_(b, a)), (mul_(c, as_elem(82))))), m));
	assert(eq_(temp_96_0, temp_96_1)) by {
		lemma_mul_comm(mul_(c, as_elem(82)), mul_(b, a));
		cong_mod_(mul_(mul_(c, as_elem(82)), mul_(b, a)), m, mul_(mul_(b, a), mul_(c, as_elem(82))), m);
		lemma_eq_ref(m);
	}
	let temp_97_0 = (mul_((add_((mod_(c, m)), b)), (mod_((mul_(a, d)), m))));
	let temp_97_1 = (mul_((add_(b, (mod_(c, m)))), (mod_((mul_(a, d)), m))));
	assert(eq_(temp_97_0, temp_97_1)) by {
		lemma_add_comm(mod_(c, m), b);
		cong_mul_(add_(mod_(c, m), b), mod_(mul_(a, d), m), add_(b, mod_(c, m)), mod_(mul_(a, d), m));
		lemma_eq_ref(mod_(mul_(a, d), m));
	}
	let temp_98_0 = (mul_((mul_(a, (mod_(d, m)))), (mul_(a, c))));
	let temp_98_1 = (mul_((mul_((mod_(d, m)), a)), (mul_(a, c))));
	assert(eq_(temp_98_0, temp_98_1)) by {
		lemma_mul_comm(a, mod_(d, m));
		cong_mul_(mul_(a, mod_(d, m)), mul_(a, c), mul_(mod_(d, m), a), mul_(a, c));
		lemma_eq_ref(mul_(a, c));
	}
	let temp_99_0 = (mul_((mul_(d, (mod_(b, m)))), (mul_(c, b))));
	let temp_99_1 = (mul_((mul_(d, (mod_((add_((mul_((mul_((mul_(c, d)), a)), m)), b)), m)))), (mul_(c, b))));
	assert(eq_(temp_99_0, temp_99_1)) by {
		lemma_mod_mul_vanish(b, mul_(mul_(c, d), a), m);
		cong_mul_(mul_(d, mod_(b, m)), mul_(c, b), mul_(d, mod_(add_(mul_(mul_(mul_(c, d), a), m), b), m)), mul_(c, b));
		lemma_eq_ref(d);
		cong_mul_(d, mod_(b, m), d, mod_(add_(mul_(mul_(mul_(c, d), a), m), b), m));
		lemma_eq_ref(mul_(c, b));
	}
	let temp_100_0 = (add_((mul_((mod_(d, m)), a)), (add_(a, c))));
	let temp_100_1 = (add_((mul_((mod_((sub_(d, (mul_((add_((mul_(d, a)), (mul_(b, d)))), m)))), m)), a)), (add_(a, c))));
	assert(eq_(temp_100_0, temp_100_1)) by {
		lemma_mod_mul_vanish(d, add_(mul_(d, a), mul_(b, d)), m);
		cong_add_(mul_(mod_(d, m), a), add_(a, c), mul_(mod_(sub_(d, mul_(add_(mul_(d, a), mul_(b, d)), m)), m), a), add_(a, c));
		lemma_eq_ref(a);
		cong_mul_(mod_(d, m), a, mod_(sub_(d, mul_(add_(mul_(d, a), mul_(b, d)), m)), m), a);
		lemma_eq_ref(add_(a, c));
	}
	let temp_101_0 = (mul_((mul_(b, c)), (mul_(b, b))));
	let temp_101_1 = (mul_((mul_((mul_(b, c)), b)), b));
	assert(eq_(temp_101_0, temp_101_1)) by {
		lemma_mul_assoc(mul_(b, c), b, b);
	}
	let temp_102_0 = (mul_((mul_(a, c)), (mod_((mul_(c, d)), m))));
	let temp_102_1 = (mul_((mul_(c, a)), (mod_((mul_(c, d)), m))));
	assert(eq_(temp_102_0, temp_102_1)) by {
		lemma_mul_comm(a, c);
		cong_mul_(mul_(a, c), mod_(mul_(c, d), m), mul_(c, a), mod_(mul_(c, d), m));
		lemma_eq_ref(mod_(mul_(c, d), m));
	}

}

} // verus!