use builtin_macros::*;
// use builtin::*;
mod nl_basics;
use crate::nl_basics::*;
verus! {

pub proof fn free_0(a: Elem, b: Elem, c: Elem, d: Elem, m: Elem)
{
	let temp_0_0 = (mul_((mul_(d, c)), (add_(d, b))));
	let temp_0_1 = (mul_((add_(d, b)), (mul_(d, c))));
	assert(eq_(temp_0_0, temp_0_1)) by {
		lemma_mul_comm(mul_(d, c), add_(d, b));
	}
	let temp_1_0 = (mod_((mul_((mod_((mul_(a, c)), m)), (mul_(b, c)))), m));
	let temp_1_1 = (mod_((mul_((mul_(b, c)), (mod_((mul_(a, c)), m)))), m));
	assert(eq_(temp_1_0, temp_1_1)) by {
		lemma_eq_ref(m);
		lemma_mul_comm(mod_(mul_(a, c), m), mul_(b, c));
		cong_mod_(mul_(mod_(mul_(a, c), m), mul_(b, c)), m, mul_(mul_(b, c), mod_(mul_(a, c), m)), m);
	}
	let temp_2_0 = (mul_((sub_(c, b)), (sub_(c, c))));
	let temp_2_1 = (mul_((sub_(c, c)), (sub_(c, b))));
	assert(eq_(temp_2_0, temp_2_1)) by {
		lemma_mul_comm(sub_(c, b), sub_(c, c));
	}
	let temp_3_0 = (mul_((mul_(a, d)), (mul_(d, c))));
	let temp_3_1 = (mul_((mul_(d, a)), (mul_(d, c))));
	assert(eq_(temp_3_0, temp_3_1)) by {
		cong_mul_(mul_(a, d), mul_(d, c), mul_(d, a), mul_(d, c));
		lemma_mul_comm(a, d);
		lemma_eq_ref(mul_(d, c));
	}
	let temp_4_0 = (mul_((mul_(a, c)), (add_(c, c))));
	let temp_4_1 = (mul_(a, (mul_(c, (add_(c, c))))));
	assert(eq_(temp_4_0, temp_4_1)) by {
		lemma_eq_sym(temp_4_1, temp_4_0);
		lemma_mul_assoc(a, c, add_(c, c));
	}
	let temp_5_0 = (mul_((add_(a, c)), (mul_(a, b))));
	let temp_5_1 = (mul_((add_(c, a)), (mul_(a, b))));
	assert(eq_(temp_5_0, temp_5_1)) by {
		cong_mul_(add_(a, c), mul_(a, b), add_(c, a), mul_(a, b));
		lemma_add_comm(a, c);
		lemma_eq_ref(mul_(a, b));
	}
	let temp_6_0 = (mul_((mul_(c, d)), (mul_(c, a))));
	let temp_6_1 = (mul_((mul_(c, d)), (mul_(a, c))));
	assert(eq_(temp_6_0, temp_6_1)) by {
		cong_mul_(mul_(c, d), mul_(c, a), mul_(c, d), mul_(a, c));
		lemma_mul_comm(c, a);
		lemma_eq_ref(mul_(c, d));
	}
	let temp_7_0 = (mul_((mul_(b, (mod_(b, m)))), (mul_(as_elem(55), b))));
	let temp_7_1 = (mul_((mul_(b, (mod_(b, m)))), (mul_(b, as_elem(55)))));
	assert(eq_(temp_7_0, temp_7_1)) by {
		lemma_mul_comm(as_elem(55), b);
		cong_mul_(mul_(b, mod_(b, m)), mul_(as_elem(55), b), mul_(b, mod_(b, m)), mul_(b, as_elem(55)));
		lemma_eq_ref(mul_(b, mod_(b, m)));
	}
	let temp_8_0 = (mul_((add_(a, d)), (mul_(c, (mod_(c, m))))));
	let temp_8_1 = (mul_((add_(a, d)), (mul_(c, (mod_((add_(c, (mul_((mul_((mul_(b, c)), (mul_(a, d)))), m)))), m))))));
	assert(eq_(temp_8_0, temp_8_1)) by {
		lemma_mod_mul_vanish(c, mul_(mul_(b, c), mul_(a, d)), m);
		cong_mul_(add_(a, d), mul_(c, mod_(c, m)), add_(a, d), mul_(c, mod_(add_(c, mul_(mul_(mul_(b, c), mul_(a, d)), m)), m)));
		lemma_eq_ref(c);
		cong_mul_(c, mod_(c, m), c, mod_(add_(c, mul_(mul_(mul_(b, c), mul_(a, d)), m)), m));
		lemma_eq_ref(add_(a, d));
	}
	let temp_9_0 = (add_((add_((mod_(c, m)), b)), (mul_(c, a))));
	let temp_9_1 = (add_((add_((mod_(c, m)), b)), (mul_(a, c))));
	assert(eq_(temp_9_0, temp_9_1)) by {
		lemma_mul_comm(c, a);
		cong_add_(add_(mod_(c, m), b), mul_(c, a), add_(mod_(c, m), b), mul_(a, c));
		lemma_eq_ref(add_(mod_(c, m), b));
	}
	let temp_10_0 = (sub_((mul_(b, a)), (mul_(as_elem(7), d))));
	let temp_10_1 = (sub_((mul_(a, b)), (mul_(as_elem(7), d))));
	assert(eq_(temp_10_0, temp_10_1)) by {
		lemma_mul_comm(b, a);
		cong_sub_(mul_(b, a), mul_(as_elem(7), d), mul_(a, b), mul_(as_elem(7), d));
		lemma_eq_ref(mul_(as_elem(7), d));
	}
	let temp_11_0 = (mul_((sub_(d, (mod_(c, m)))), (mod_((mul_(d, as_elem(60))), m))));
	let temp_11_1 = (mul_((sub_(d, (mod_(c, m)))), (mod_((add_((mul_((mul_((sub_((mod_(a, m)), d)), (mul_(a, d)))), m)), (mul_(d, as_elem(60))))), m))));
	assert(eq_(temp_11_0, temp_11_1)) by {
		lemma_mod_mul_vanish(mul_(d, as_elem(60)), mul_(sub_(mod_(a, m), d), mul_(a, d)), m);
		cong_mul_(sub_(d, mod_(c, m)), mod_(mul_(d, as_elem(60)), m), sub_(d, mod_(c, m)), mod_(add_(mul_(mul_(sub_(mod_(a, m), d), mul_(a, d)), m), mul_(d, as_elem(60))), m));
		lemma_eq_ref(sub_(d, mod_(c, m)));
	}
	let temp_12_0 = (mul_((mul_((mod_(a, m)), d)), (mod_((sub_(b, a)), m))));
	let temp_12_1 = (mul_((mul_((mod_(a, m)), d)), (mod_((sub_((mod_(b, m)), (mod_(a, m)))), m))));
	assert(eq_(temp_12_0, temp_12_1)) by {
		cong_mul_(mul_(mod_(a, m), d), mod_(sub_(b, a), m), mul_(mod_(a, m), d), mod_(sub_(mod_(b, m), mod_(a, m)), m));
		lemma_mod_sub_noop(b, a, m);
		lemma_eq_ref(mul_(mod_(a, m), d));
	}
	let temp_13_0 = (mul_((mul_(d, b)), (mul_(c, c))));
	let temp_13_1 = (mul_((mul_((mul_(d, b)), c)), c));
	assert(eq_(temp_13_0, temp_13_1)) by {
		lemma_mul_assoc(mul_(d, b), c, c);
	}
	let temp_14_0 = (mul_((mul_(d, c)), (sub_(d, c))));
	let temp_14_1 = (mul_((sub_(d, c)), (mul_(d, c))));
	assert(eq_(temp_14_0, temp_14_1)) by {
		lemma_mul_comm(mul_(d, c), sub_(d, c));
	}
	let temp_15_0 = (mul_((mul_(a, b)), (mul_(a, a))));
	let temp_15_1 = (mul_((mul_(a, b)), (mul_(a, a))));
	assert(eq_(temp_15_0, temp_15_1)) by {
		lemma_eq_ref(temp_15_0);
	}
	let temp_16_0 = (add_((sub_(a, d)), (mod_((sub_((mod_(b, m)), c)), m))));
	let temp_16_1 = (add_((sub_(a, d)), (mod_((sub_((sub_((mod_(b, m)), c)), (mul_((mod_((mul_((mul_(as_elem(77), a)), (mul_(c, b)))), m)), m)))), m))));
	assert(eq_(temp_16_0, temp_16_1)) by {
		cong_add_(sub_(a, d), mod_(sub_(mod_(b, m), c), m), sub_(a, d), mod_(sub_(sub_(mod_(b, m), c), mul_(mod_(mul_(mul_(as_elem(77), a), mul_(c, b)), m), m)), m));
		lemma_mod_mul_vanish(sub_(mod_(b, m), c), mod_(mul_(mul_(as_elem(77), a), mul_(c, b)), m), m);
		lemma_eq_ref(sub_(a, d));
	}
	let temp_17_0 = (mul_((mod_((mul_(b, (mod_(b, m)))), m)), (mul_(b, c))));
	let temp_17_1 = (mul_((mul_((mod_((mul_(b, (mod_(b, m)))), m)), b)), c));
	assert(eq_(temp_17_0, temp_17_1)) by {
		lemma_mul_assoc(mod_(mul_(b, mod_(b, m)), m), b, c);
	}
	let temp_18_0 = (sub_((sub_(a, c)), (mul_(d, b))));
	let temp_18_1 = (sub_((sub_(a, c)), (mul_(b, d))));
	assert(eq_(temp_18_0, temp_18_1)) by {
		cong_sub_(sub_(a, c), mul_(d, b), sub_(a, c), mul_(b, d));
		lemma_mul_comm(d, b);
		lemma_eq_ref(sub_(a, c));
	}
	let temp_19_0 = (mul_((mul_(d, a)), (mul_(a, (mod_(c, m))))));
	let temp_19_1 = (mul_(d, (mul_(a, (mul_(a, (mod_(c, m))))))));
	assert(eq_(temp_19_0, temp_19_1)) by {
		lemma_mul_assoc(d, a, mul_(a, mod_(c, m)));
		lemma_eq_sym(temp_19_1, temp_19_0);
	}
	let temp_20_0 = (mul_((sub_(a, d)), (mul_(d, as_elem(69)))));
	let temp_20_1 = (sub_((mul_(a, (mul_(d, as_elem(69))))), (mul_(d, (mul_(d, as_elem(69)))))));
	assert(eq_(temp_20_0, temp_20_1)) by {
		lemma_mul_dist(mul_(d, as_elem(69)), a, d);
	}
	let temp_21_0 = (sub_((mul_(a, c)), (mul_(c, a))));
	let temp_21_1 = (sub_((mul_(a, c)), (mul_(a, c))));
	assert(eq_(temp_21_0, temp_21_1)) by {
		cong_sub_(mul_(a, c), mul_(c, a), mul_(a, c), mul_(a, c));
		lemma_mul_comm(c, a);
		lemma_eq_ref(mul_(a, c));
	}
	let temp_22_0 = (mul_((add_(d, b)), c));
	let temp_22_1 = (mul_(c, (add_(d, b))));
	assert(eq_(temp_22_0, temp_22_1)) by {
		lemma_mul_comm(add_(d, b), c);
	}
	let temp_23_0 = (mul_((mul_(d, (mod_(b, m)))), (mul_(c, a))));
	let temp_23_1 = (mul_((mul_(d, (mod_((sub_(b, (mul_((mul_((mul_(d, (mod_(a, m)))), (mul_((mod_(a, m)), c)))), m)))), m)))), (mul_(c, a))));
	assert(eq_(temp_23_0, temp_23_1)) by {
		lemma_mod_mul_vanish(b, mul_(mul_(d, mod_(a, m)), mul_(mod_(a, m), c)), m);
		cong_mul_(mul_(d, mod_(b, m)), mul_(c, a), mul_(d, mod_(sub_(b, mul_(mul_(mul_(d, mod_(a, m)), mul_(mod_(a, m), c)), m)), m)), mul_(c, a));
		lemma_eq_ref(d);
		cong_mul_(d, mod_(b, m), d, mod_(sub_(b, mul_(mul_(mul_(d, mod_(a, m)), mul_(mod_(a, m), c)), m)), m));
		lemma_eq_ref(mul_(c, a));
	}
	let temp_24_0 = (mul_((mul_(d, (mod_(a, m)))), (mul_(c, (mod_(c, m))))));
	let temp_24_1 = (mul_((mul_(d, (mod_((sub_(a, (mul_((mul_((mul_(c, (mod_(b, m)))), (sub_(as_elem(72), b)))), m)))), m)))), (mul_(c, (mod_(c, m))))));
	assert(eq_(temp_24_0, temp_24_1)) by {
		cong_mul_(mul_(d, mod_(a, m)), mul_(c, mod_(c, m)), mul_(d, mod_(sub_(a, mul_(mul_(mul_(c, mod_(b, m)), sub_(as_elem(72), b)), m)), m)), mul_(c, mod_(c, m)));
		lemma_mod_mul_vanish(a, mul_(mul_(c, mod_(b, m)), sub_(as_elem(72), b)), m);
		lemma_eq_ref(d);
		lemma_eq_ref(mul_(c, mod_(c, m)));
		cong_mul_(d, mod_(a, m), d, mod_(sub_(a, mul_(mul_(mul_(c, mod_(b, m)), sub_(as_elem(72), b)), m)), m));
	}
	let temp_25_0 = (mod_((add_((mod_((mul_(a, d)), m)), (add_(d, b)))), m));
	let temp_25_1 = (mod_((add_((mod_((mul_(a, d)), m)), (mod_((add_(d, b)), m)))), m));
	assert(eq_(temp_25_0, temp_25_1)) by {
		lemma_mod_add_noop(mod_(mul_(a, d), m), add_(d, b), m);
	}
	let temp_26_0 = (add_((mod_((mul_((mod_(b, m)), b)), m)), (mod_((mul_(c, d)), m))));
	let temp_26_1 = (add_((mod_((mul_((mod_(b, m)), b)), m)), (mod_((mul_(d, c)), m))));
	assert(eq_(temp_26_0, temp_26_1)) by {
		lemma_mul_comm(c, d);
		cong_add_(mod_(mul_(mod_(b, m), b), m), mod_(mul_(c, d), m), mod_(mul_(mod_(b, m), b), m), mod_(mul_(d, c), m));
		lemma_eq_ref(m);
		cong_mod_(mul_(c, d), m, mul_(d, c), m);
		lemma_eq_ref(mod_(mul_(mod_(b, m), b), m));
	}
	let temp_27_0 = (mul_((mul_(c, a)), (mul_(b, a))));
	let temp_27_1 = (mul_(c, (mul_(a, (mul_(b, a))))));
	assert(eq_(temp_27_0, temp_27_1)) by {
		lemma_eq_sym(temp_27_1, temp_27_0);
		lemma_mul_assoc(c, a, mul_(b, a));
	}
	let temp_28_0 = (mod_((mul_((mul_(c, c)), (mul_(c, d)))), m));
	let temp_28_1 = (mod_((mul_((mul_(c, d)), (mul_(c, c)))), m));
	assert(eq_(temp_28_0, temp_28_1)) by {
		cong_mod_(mul_(mul_(c, c), mul_(c, d)), m, mul_(mul_(c, d), mul_(c, c)), m);
		lemma_mul_comm(mul_(c, c), mul_(c, d));
		lemma_eq_ref(m);
	}
	let temp_29_0 = (sub_((add_(b, d)), (mul_((mod_(a, m)), c))));
	let temp_29_1 = (sub_((add_(b, d)), (mul_(c, (mod_(a, m))))));
	assert(eq_(temp_29_0, temp_29_1)) by {
		lemma_mul_comm(mod_(a, m), c);
		cong_sub_(add_(b, d), mul_(mod_(a, m), c), add_(b, d), mul_(c, mod_(a, m)));
		lemma_eq_ref(add_(b, d));
	}
	let temp_30_0 = (mul_((sub_(a, d)), (mul_(c, as_elem(46)))));
	let temp_30_1 = (mul_((mul_((sub_(a, d)), c)), as_elem(46)));
	assert(eq_(temp_30_0, temp_30_1)) by {
		lemma_mul_assoc(sub_(a, d), c, as_elem(46));
	}
	let temp_31_0 = (mul_((mul_(c, a)), (mul_(b, a))));
	let temp_31_1 = (mul_(c, (mul_(a, (mul_(b, a))))));
	assert(eq_(temp_31_0, temp_31_1)) by {
		lemma_eq_sym(temp_31_1, temp_31_0);
		lemma_mul_assoc(c, a, mul_(b, a));
	}
	let temp_32_0 = (mul_((mul_(b, c)), (mul_(b, c))));
	let temp_32_1 = (mul_(b, (mul_(c, (mul_(b, c))))));
	assert(eq_(temp_32_0, temp_32_1)) by {
		lemma_eq_sym(temp_32_1, temp_32_0);
		lemma_mul_assoc(b, c, mul_(b, c));
	}
	let temp_33_0 = (mul_((mul_(c, d)), (mul_(a, (mod_(d, m))))));
	let temp_33_1 = (mul_((mul_(c, d)), (mul_((mod_(d, m)), a))));
	assert(eq_(temp_33_0, temp_33_1)) by {
		lemma_mul_comm(a, mod_(d, m));
		cong_mul_(mul_(c, d), mul_(a, mod_(d, m)), mul_(c, d), mul_(mod_(d, m), a));
		lemma_eq_ref(mul_(c, d));
	}
	let temp_34_0 = (mul_((mul_(b, a)), (mul_(d, b))));
	let temp_34_1 = (mul_((mul_(a, b)), (mul_(d, b))));
	assert(eq_(temp_34_0, temp_34_1)) by {
		lemma_eq_ref(mul_(d, b));
		cong_mul_(mul_(b, a), mul_(d, b), mul_(a, b), mul_(d, b));
		lemma_mul_comm(b, a);
	}
	let temp_35_0 = (mul_((mod_((mul_(d, a)), m)), (mul_(c, b))));
	let temp_35_1 = (mul_((mod_((mul_(a, d)), m)), (mul_(c, b))));
	assert(eq_(temp_35_0, temp_35_1)) by {
		lemma_mul_comm(d, a);
		cong_mul_(mod_(mul_(d, a), m), mul_(c, b), mod_(mul_(a, d), m), mul_(c, b));
		cong_mod_(mul_(d, a), m, mul_(a, d), m);
		lemma_eq_ref(mul_(c, b));
		lemma_eq_ref(m);
	}
	let temp_36_0 = (mul_((mul_(d, (mod_(b, m)))), (add_(b, b))));
	let temp_36_1 = (mul_(d, (mul_((mod_(b, m)), (add_(b, b))))));
	assert(eq_(temp_36_0, temp_36_1)) by {
		lemma_eq_sym(temp_36_1, temp_36_0);
		lemma_mul_assoc(d, mod_(b, m), add_(b, b));
	}
	let temp_37_0 = (mul_((mul_(a, a)), (add_((mod_(c, m)), b))));
	let temp_37_1 = (mul_(a, (mul_(a, (add_((mod_(c, m)), b))))));
	assert(eq_(temp_37_0, temp_37_1)) by {
		lemma_mul_assoc(a, a, add_(mod_(c, m), b));
		lemma_eq_sym(temp_37_1, temp_37_0);
	}
	let temp_38_0 = (mul_((mul_(b, d)), (mul_(d, b))));
	let temp_38_1 = (mul_((mul_((mul_(b, d)), d)), b));
	assert(eq_(temp_38_0, temp_38_1)) by {
		lemma_mul_assoc(mul_(b, d), d, b);
	}
	let temp_39_0 = (mul_((mul_(c, a)), (mul_(c, c))));
	let temp_39_1 = (mul_((mul_(c, a)), (mul_(c, c))));
	assert(eq_(temp_39_0, temp_39_1)) by {
		lemma_eq_ref(temp_39_0);
	}
	let temp_40_0 = (mul_((mul_(b, b)), (mod_((sub_(c, b)), m))));
	let temp_40_1 = (mul_((mul_(b, b)), (mod_((sub_((sub_(c, b)), (mul_((add_((sub_(b, d)), (mod_((mul_((mod_(a, m)), (mod_(b, m)))), m)))), m)))), m))));
	assert(eq_(temp_40_0, temp_40_1)) by {
		lemma_mul_comm(b, b);
		cong_mul_(mul_(b, b), mod_(sub_(c, b), m), mul_(b, b), mod_(sub_(sub_(c, b), mul_(add_(sub_(b, d), mod_(mul_(mod_(a, m), mod_(b, m)), m)), m)), m));
		lemma_mod_mul_vanish(sub_(c, b), add_(sub_(b, d), mod_(mul_(mod_(a, m), mod_(b, m)), m)), m);
	}
	let temp_41_0 = (sub_((mul_((mod_(d, m)), b)), (mul_(a, b))));
	let temp_41_1 = (sub_((mul_(b, (mod_(d, m)))), (mul_(a, b))));
	assert(eq_(temp_41_0, temp_41_1)) by {
		lemma_mul_comm(mod_(d, m), b);
		cong_sub_(mul_(mod_(d, m), b), mul_(a, b), mul_(b, mod_(d, m)), mul_(a, b));
		lemma_eq_ref(mul_(a, b));
	}
	let temp_42_0 = (mul_((mul_((mod_(c, m)), d)), (mul_((mod_(d, m)), c))));
	let temp_42_1 = (mul_((mul_((mod_(c, m)), d)), (mul_((mod_((sub_(d, (mul_((mul_((mul_(b, b)), (mul_(c, b)))), m)))), m)), c))));
	assert(eq_(temp_42_0, temp_42_1)) by {
		lemma_mod_mul_vanish(d, mul_(mul_(b, b), mul_(c, b)), m);
		cong_mul_(mul_(mod_(c, m), d), mul_(mod_(d, m), c), mul_(mod_(c, m), d), mul_(mod_(sub_(d, mul_(mul_(mul_(b, b), mul_(c, b)), m)), m), c));
		lemma_eq_ref(c);
		lemma_eq_ref(mul_(mod_(c, m), d));
		cong_mul_(mod_(d, m), c, mod_(sub_(d, mul_(mul_(mul_(b, b), mul_(c, b)), m)), m), c);
	}
	let temp_43_0 = (sub_((mul_(b, a)), (mul_(a, d))));
	let temp_43_1 = (sub_((mul_(b, a)), (mul_(d, a))));
	assert(eq_(temp_43_0, temp_43_1)) by {
		cong_sub_(mul_(b, a), mul_(a, d), mul_(b, a), mul_(d, a));
		lemma_mul_comm(a, d);
		lemma_eq_ref(mul_(b, a));
	}
	let temp_44_0 = (sub_((mul_(a, b)), (mul_(c, a))));
	let temp_44_1 = (sub_((mul_(a, b)), (mul_(a, c))));
	assert(eq_(temp_44_0, temp_44_1)) by {
		cong_sub_(mul_(a, b), mul_(c, a), mul_(a, b), mul_(a, c));
		lemma_mul_comm(c, a);
		lemma_eq_ref(mul_(a, b));
	}
	let temp_45_0 = (mul_((mul_((mod_(a, m)), (mod_(a, m)))), (mul_(b, b))));
	let temp_45_1 = (mul_((mul_((mod_((add_(a, (mul_((mul_((mod_((mul_(d, c)), m)), (mul_(d, b)))), m)))), m)), (mod_(a, m)))), (mul_(b, b))));
	assert(eq_(temp_45_0, temp_45_1)) by {
		lemma_mul_comm(b, b);
		lemma_mod_mul_vanish(a, mul_(mod_(mul_(d, c), m), mul_(d, b)), m);
		cong_mul_(mul_(mod_(a, m), mod_(a, m)), mul_(b, b), mul_(mod_(add_(a, mul_(mul_(mod_(mul_(d, c), m), mul_(d, b)), m)), m), mod_(a, m)), mul_(b, b));
		cong_mul_(mod_(a, m), mod_(a, m), mod_(add_(a, mul_(mul_(mod_(mul_(d, c), m), mul_(d, b)), m)), m), mod_(a, m));
		lemma_eq_ref(mod_(a, m));
	}
	let temp_46_0 = (mul_((mod_((mul_(a, a)), m)), (mul_((mod_(b, m)), (mod_(b, m))))));
	let temp_46_1 = (mul_((mul_((mod_((mul_(a, a)), m)), (mod_(b, m)))), (mod_(b, m))));
	assert(eq_(temp_46_0, temp_46_1)) by {
		lemma_mul_assoc(mod_(mul_(a, a), m), mod_(b, m), mod_(b, m));
	}
	let temp_47_0 = (add_((mul_(a, d)), d));
	let temp_47_1 = (add_(d, (mul_(a, d))));
	assert(eq_(temp_47_0, temp_47_1)) by {
		lemma_add_comm(mul_(a, d), d);
	}
	let temp_48_0 = (mod_((mul_((sub_(b, a)), (sub_(b, d)))), m));
	let temp_48_1 = (mod_((add_((mul_((mul_((mod_((add_(a, (mod_(c, m)))), m)), (mul_(c, c)))), m)), (mul_((sub_(b, a)), (sub_(b, d)))))), m));
	assert(eq_(temp_48_0, temp_48_1)) by {
		lemma_mod_mul_vanish(mul_(sub_(b, a), sub_(b, d)), mul_(mod_(add_(a, mod_(c, m)), m), mul_(c, c)), m);
	}
	let temp_49_0 = (add_((mul_(b, c)), (mul_(b, d))));
	let temp_49_1 = (mul_(b, (add_(c, d))));
	assert(eq_(temp_49_0, temp_49_1)) by {
		lemma_eq_sym(temp_49_1, temp_49_0);
		lemma_mul_dist(b, c, d);
	}
	let temp_50_0 = (mul_((add_(b, b)), (mul_(d, a))));
	let temp_50_1 = (mul_((add_(b, b)), (mul_(d, a))));
	assert(eq_(temp_50_0, temp_50_1)) by {
		lemma_eq_ref(temp_50_0);
	}
	let temp_51_0 = (sub_((add_(c, a)), (mul_((mod_(d, m)), d))));
	let temp_51_1 = (sub_((add_(a, c)), (mul_((mod_(d, m)), d))));
	assert(eq_(temp_51_0, temp_51_1)) by {
		lemma_eq_ref(mul_(mod_(d, m), d));
		lemma_add_comm(c, a);
		cong_sub_(add_(c, a), mul_(mod_(d, m), d), add_(a, c), mul_(mod_(d, m), d));
	}
	let temp_52_0 = (mod_((mul_((mul_(a, a)), (mul_(d, d)))), m));
	let temp_52_1 = (mod_((mul_((mul_(a, a)), (mul_(d, d)))), m));
	assert(eq_(temp_52_0, temp_52_1)) by {
		lemma_eq_ref(temp_52_0);
	}
	let temp_53_0 = (mod_((mul_((mul_(c, c)), (sub_(d, d)))), m));
	let temp_53_1 = (mod_((add_((mul_((mul_((mul_(as_elem(9), d)), (add_(b, a)))), m)), (mul_((mul_(c, c)), (sub_(d, d)))))), m));
	assert(eq_(temp_53_0, temp_53_1)) by {
		lemma_mod_mul_vanish(mul_(mul_(c, c), sub_(d, d)), mul_(mul_(as_elem(9), d), add_(b, a)), m);
	}
	let temp_54_0 = (mod_((mul_((mul_(d, d)), (sub_(a, a)))), m));
	let temp_54_1 = (mod_((mul_(d, (mul_(d, (sub_(a, a)))))), m));
	assert(eq_(temp_54_0, temp_54_1)) by {
		lemma_mul_assoc(d, d, sub_(a, a));
		cong_mod_(mul_(mul_(d, d), sub_(a, a)), m, mul_(d, mul_(d, sub_(a, a))), m);
		lemma_eq_sym(mul_(d, mul_(d, sub_(a, a))), mul_(mul_(d, d), sub_(a, a)));
		lemma_eq_ref(m);
	}
	let temp_55_0 = (mul_((mul_(c, as_elem(22))), (sub_(b, c))));
	let temp_55_1 = (mul_((mul_(as_elem(22), c)), (sub_(b, c))));
	assert(eq_(temp_55_0, temp_55_1)) by {
		cong_mul_(mul_(c, as_elem(22)), sub_(b, c), mul_(as_elem(22), c), sub_(b, c));
		lemma_mul_comm(c, as_elem(22));
		lemma_eq_ref(sub_(b, c));
	}
	let temp_56_0 = (add_((add_(c, as_elem(65))), (mod_((mul_(c, c)), m))));
	let temp_56_1 = (add_((mod_((mul_(c, c)), m)), (add_(c, as_elem(65)))));
	assert(eq_(temp_56_0, temp_56_1)) by {
		lemma_add_comm(add_(c, as_elem(65)), mod_(mul_(c, c), m));
	}
	let temp_57_0 = (mul_((sub_((mod_(b, m)), (mod_(b, m)))), (mul_((mod_(a, m)), b))));
	let temp_57_1 = (mul_((sub_((mod_(b, m)), (mod_(b, m)))), (mul_(b, (mod_(a, m))))));
	assert(eq_(temp_57_0, temp_57_1)) by {
		lemma_mul_comm(mod_(a, m), b);
		cong_mul_(sub_(mod_(b, m), mod_(b, m)), mul_(mod_(a, m), b), sub_(mod_(b, m), mod_(b, m)), mul_(b, mod_(a, m)));
		lemma_eq_ref(sub_(mod_(b, m), mod_(b, m)));
	}
	let temp_58_0 = (mul_((mul_(b, (mod_(a, m)))), (mul_(a, b))));
	let temp_58_1 = (mul_((mul_(b, (mod_((add_((mul_((mul_((mul_(d, as_elem(94))), (mul_(b, b)))), m)), a)), m)))), (mul_(a, b))));
	assert(eq_(temp_58_0, temp_58_1)) by {
		lemma_mod_mul_vanish(a, mul_(mul_(d, as_elem(94)), mul_(b, b)), m);
		cong_mul_(mul_(b, mod_(a, m)), mul_(a, b), mul_(b, mod_(add_(mul_(mul_(mul_(d, as_elem(94)), mul_(b, b)), m), a), m)), mul_(a, b));
		lemma_eq_ref(b);
		cong_mul_(b, mod_(a, m), b, mod_(add_(mul_(mul_(mul_(d, as_elem(94)), mul_(b, b)), m), a), m));
		lemma_eq_ref(mul_(a, b));
	}
	let temp_59_0 = (add_((mod_((add_(d, c)), m)), (mul_(c, (mod_(c, m))))));
	let temp_59_1 = (add_((mul_(c, (mod_(c, m)))), (mod_((add_(d, c)), m))));
	assert(eq_(temp_59_0, temp_59_1)) by {
		lemma_add_comm(mod_(add_(d, c), m), mul_(c, mod_(c, m)));
	}
	let temp_60_0 = (add_((mod_((mul_(d, a)), m)), (mul_(b, d))));
	let temp_60_1 = (add_((mod_((mul_(d, a)), m)), (mul_(d, b))));
	assert(eq_(temp_60_0, temp_60_1)) by {
		lemma_mul_comm(b, d);
		cong_add_(mod_(mul_(d, a), m), mul_(b, d), mod_(mul_(d, a), m), mul_(d, b));
		lemma_eq_ref(mod_(mul_(d, a), m));
	}
	let temp_61_0 = (mul_((mul_(c, a)), (mul_(d, c))));
	let temp_61_1 = (mul_((mul_(c, a)), (mul_(c, d))));
	assert(eq_(temp_61_0, temp_61_1)) by {
		cong_mul_(mul_(c, a), mul_(d, c), mul_(c, a), mul_(c, d));
		lemma_mul_comm(d, c);
		lemma_eq_ref(mul_(c, a));
	}
	let temp_62_0 = (mul_((mul_(d, c)), (mul_((mod_(b, m)), d))));
	let temp_62_1 = (mul_((mul_((mul_(d, c)), (mod_(b, m)))), d));
	assert(eq_(temp_62_0, temp_62_1)) by {
		lemma_mul_assoc(mul_(d, c), mod_(b, m), d);
	}
	let temp_63_0 = (mul_((add_(d, c)), (mul_(b, c))));
	let temp_63_1 = (mul_((add_(c, d)), (mul_(b, c))));
	assert(eq_(temp_63_0, temp_63_1)) by {
		cong_mul_(add_(d, c), mul_(b, c), add_(c, d), mul_(b, c));
		lemma_add_comm(d, c);
		lemma_eq_ref(mul_(b, c));
	}
	let temp_64_0 = (mul_((mul_(d, a)), (add_(c, c))));
	let temp_64_1 = (mul_(d, (mul_(a, (add_(c, c))))));
	assert(eq_(temp_64_0, temp_64_1)) by {
		lemma_eq_sym(temp_64_1, temp_64_0);
		lemma_mul_assoc(d, a, add_(c, c));
	}
	let temp_65_0 = (mul_((sub_(d, a)), (mod_((mul_(a, c)), m))));
	let temp_65_1 = (sub_((mul_(d, (mod_((mul_(a, c)), m)))), (mul_(a, (mod_((mul_(a, c)), m))))));
	assert(eq_(temp_65_0, temp_65_1)) by {
		lemma_mul_dist(mod_(mul_(a, c), m), d, a);
	}
	let temp_66_0 = (add_((mul_(c, a)), (mul_(a, d))));
	let temp_66_1 = (add_((mul_(a, c)), (mul_(a, d))));
	assert(eq_(temp_66_0, temp_66_1)) by {
		cong_add_(mul_(c, a), mul_(a, d), mul_(a, c), mul_(a, d));
		lemma_mul_comm(c, a);
		lemma_eq_ref(mul_(a, d));
	}
	let temp_67_0 = (add_((mod_((mul_(b, b)), m)), (mod_((mul_(d, (mod_(a, m)))), m))));
	let temp_67_1 = (add_((mod_((add_((mul_((mul_((mod_((sub_(c, b)), m)), (mul_(b, b)))), m)), (mul_(b, b)))), m)), (mod_((mul_(d, (mod_(a, m)))), m))));
	assert(eq_(temp_67_0, temp_67_1)) by {
		lemma_mod_mul_vanish(mul_(b, b), mul_(mod_(sub_(c, b), m), mul_(b, b)), m);
		cong_add_(mod_(mul_(b, b), m), mod_(mul_(d, mod_(a, m)), m), mod_(add_(mul_(mul_(mod_(sub_(c, b), m), mul_(b, b)), m), mul_(b, b)), m), mod_(mul_(d, mod_(a, m)), m));
		lemma_eq_ref(mod_(mul_(d, mod_(a, m)), m));
	}
	let temp_68_0 = (mul_((mul_(d, as_elem(5))), (mod_((mul_(d, (mod_(c, m)))), m))));
	let temp_68_1 = (mul_((mul_(d, as_elem(5))), (mod_((add_((mul_(d, (mod_(c, m)))), (mul_((mul_((mul_(a, a)), (add_((mod_(d, m)), d)))), m)))), m))));
	assert(eq_(temp_68_0, temp_68_1)) by {
		lemma_mod_mul_vanish(mul_(d, mod_(c, m)), mul_(mul_(a, a), add_(mod_(d, m), d)), m);
		cong_mul_(mul_(d, as_elem(5)), mod_(mul_(d, mod_(c, m)), m), mul_(d, as_elem(5)), mod_(add_(mul_(d, mod_(c, m)), mul_(mul_(mul_(a, a), add_(mod_(d, m), d)), m)), m));
		lemma_eq_ref(mul_(d, as_elem(5)));
	}
	let temp_69_0 = (mul_((mul_(b, b)), (mul_(b, c))));
	let temp_69_1 = (mul_((mul_(b, c)), (mul_(b, b))));
	assert(eq_(temp_69_0, temp_69_1)) by {
		lemma_mul_comm(mul_(b, b), mul_(b, c));
	}
	let temp_70_0 = (mul_((add_(b, a)), (mul_(b, c))));
	let temp_70_1 = (mul_((add_(b, a)), (mul_(c, b))));
	assert(eq_(temp_70_0, temp_70_1)) by {
		cong_mul_(add_(b, a), mul_(b, c), add_(b, a), mul_(c, b));
		lemma_mul_comm(b, c);
		lemma_eq_ref(add_(b, a));
	}
	let temp_71_0 = (sub_((mul_(d, d)), (mod_((mul_(c, b)), m))));
	let temp_71_1 = (sub_((mul_(d, d)), (mod_((mul_(c, b)), m))));
	assert(eq_(temp_71_0, temp_71_1)) by {
		lemma_eq_ref(temp_71_0);
	}
	let temp_72_0 = (mul_((add_(a, c)), (mul_(a, a))));
	let temp_72_1 = (mul_((add_(c, a)), (mul_(a, a))));
	assert(eq_(temp_72_0, temp_72_1)) by {
		cong_mul_(add_(a, c), mul_(a, a), add_(c, a), mul_(a, a));
		lemma_add_comm(a, c);
		lemma_mul_comm(a, a);
	}
	let temp_73_0 = (mul_((sub_(b, b)), (mul_(c, b))));
	let temp_73_1 = (mul_((mul_((sub_(b, b)), c)), b));
	assert(eq_(temp_73_0, temp_73_1)) by {
		lemma_mul_assoc(sub_(b, b), c, b);
	}
	let temp_74_0 = (mul_((mul_(b, d)), (mul_(b, d))));
	let temp_74_1 = (mul_((mul_(b, d)), (mul_(b, d))));
	assert(eq_(temp_74_0, temp_74_1)) by {
		lemma_eq_ref(temp_74_0);
	}
	let temp_75_0 = (mul_(a, (mul_(as_elem(17), c))));
	let temp_75_1 = (mul_((mul_(a, as_elem(17))), c));
	assert(eq_(temp_75_0, temp_75_1)) by {
		lemma_mul_assoc(a, as_elem(17), c);
	}
	let temp_76_0 = (mod_((add_((mul_(b, d)), (mul_((mod_(b, m)), d)))), m));
	let temp_76_1 = (mod_((add_((mul_((mod_((mul_((mul_((mod_(d, m)), a)), (mul_(b, as_elem(94))))), m)), m)), (add_((mul_(b, d)), (mul_((mod_(b, m)), d)))))), m));
	assert(eq_(temp_76_0, temp_76_1)) by {
		lemma_mod_mul_vanish(add_(mul_(b, d), mul_(mod_(b, m), d)), mod_(mul_(mul_(mod_(d, m), a), mul_(b, as_elem(94))), m), m);
	}
	let temp_77_0 = (mul_((mul_((mod_(b, m)), b)), (mul_(c, c))));
	let temp_77_1 = (mul_((mul_((mul_((mod_(b, m)), b)), c)), c));
	assert(eq_(temp_77_0, temp_77_1)) by {
		lemma_mul_assoc(mul_(mod_(b, m), b), c, c);
	}
	let temp_78_0 = (mul_((mul_(c, d)), (add_(c, (mod_(c, m))))));
	let temp_78_1 = (mul_(c, (mul_(d, (add_(c, (mod_(c, m))))))));
	assert(eq_(temp_78_0, temp_78_1)) by {
		lemma_eq_sym(temp_78_1, temp_78_0);
		lemma_mul_assoc(c, d, add_(c, mod_(c, m)));
	}
	let temp_79_0 = (add_((sub_(b, b)), (mul_(d, (mod_(a, m))))));
	let temp_79_1 = (add_((mul_(d, (mod_(a, m)))), (sub_(b, b))));
	assert(eq_(temp_79_0, temp_79_1)) by {
		lemma_add_comm(sub_(b, b), mul_(d, mod_(a, m)));
	}
	let temp_80_0 = (mul_((mul_(b, (mod_(a, m)))), (mul_(a, a))));
	let temp_80_1 = (mul_(b, (mul_((mod_(a, m)), (mul_(a, a))))));
	assert(eq_(temp_80_0, temp_80_1)) by {
		lemma_eq_sym(temp_80_1, temp_80_0);
		lemma_mul_assoc(b, mod_(a, m), mul_(a, a));
	}
	let temp_81_0 = (mul_((mul_(c, c)), (mul_(d, c))));
	let temp_81_1 = (mul_(c, (mul_(c, (mul_(d, c))))));
	assert(eq_(temp_81_0, temp_81_1)) by {
		lemma_eq_sym(temp_81_1, temp_81_0);
		lemma_mul_assoc(c, c, mul_(d, c));
	}
	let temp_82_0 = (mul_((mul_(a, c)), (mod_((mul_(b, a)), m))));
	let temp_82_1 = (mul_(a, (mul_(c, (mod_((mul_(b, a)), m))))));
	assert(eq_(temp_82_0, temp_82_1)) by {
		lemma_mul_assoc(a, c, mod_(mul_(b, a), m));
		lemma_eq_sym(temp_82_1, temp_82_0);
	}
	let temp_83_0 = (mul_((mul_(d, b)), (mod_((mul_(c, d)), m))));
	let temp_83_1 = (mul_((mod_((mul_(c, d)), m)), (mul_(d, b))));
	assert(eq_(temp_83_0, temp_83_1)) by {
		lemma_mul_comm(mul_(d, b), mod_(mul_(c, d), m));
	}
	let temp_84_0 = (mod_((mul_((mod_(a, m)), (mul_(b, a)))), m));
	let temp_84_1 = (mod_((mul_((mul_((mod_(a, m)), b)), a)), m));
	assert(eq_(temp_84_0, temp_84_1)) by {
		lemma_mul_assoc(mod_(a, m), b, a);
		cong_mod_(mul_(mod_(a, m), mul_(b, a)), m, mul_(mul_(mod_(a, m), b), a), m);
		lemma_eq_ref(m);
	}
	let temp_85_0 = (sub_((mod_((mul_(b, c)), m)), (mul_(d, c))));
	let temp_85_1 = (sub_((mod_((mul_(c, b)), m)), (mul_(d, c))));
	assert(eq_(temp_85_0, temp_85_1)) by {
		cong_mod_(mul_(b, c), m, mul_(c, b), m);
		lemma_eq_ref(mul_(d, c));
		lemma_eq_ref(m);
		lemma_mul_comm(b, c);
		cong_sub_(mod_(mul_(b, c), m), mul_(d, c), mod_(mul_(c, b), m), mul_(d, c));
	}
	let temp_86_0 = (mul_((mul_(a, b)), c));
	let temp_86_1 = (mul_(a, (mul_(b, c))));
	assert(eq_(temp_86_0, temp_86_1)) by {
		lemma_eq_sym(temp_86_1, temp_86_0);
		lemma_mul_assoc(a, b, c);
	}
	let temp_87_0 = (mul_((mul_(d, (mod_(b, m)))), (mul_(a, b))));
	let temp_87_1 = (mul_((mul_(d, (mod_((sub_(b, (mul_((mul_((mul_(d, c)), (mul_(c, a)))), m)))), m)))), (mul_(a, b))));
	assert(eq_(temp_87_0, temp_87_1)) by {
		cong_mul_(d, mod_(b, m), d, mod_(sub_(b, mul_(mul_(mul_(d, c), mul_(c, a)), m)), m));
		lemma_eq_ref(mul_(a, b));
		lemma_eq_ref(d);
		lemma_mod_mul_vanish(b, mul_(mul_(d, c), mul_(c, a)), m);
		cong_mul_(mul_(d, mod_(b, m)), mul_(a, b), mul_(d, mod_(sub_(b, mul_(mul_(mul_(d, c), mul_(c, a)), m)), m)), mul_(a, b));
	}
	let temp_88_0 = (mul_((mul_((mod_(as_elem(93), m)), as_elem(60))), (mul_(a, c))));
	let temp_88_1 = (mul_((mul_((mod_((add_(as_elem(93), (mul_((mul_((mul_(c, b)), (mul_(a, c)))), m)))), m)), as_elem(60))), (mul_(a, c))));
	assert(eq_(temp_88_0, temp_88_1)) by {
		lemma_mod_mul_vanish(as_elem(93), mul_(mul_(c, b), mul_(a, c)), m);
		cong_mul_(mul_(mod_(as_elem(93), m), as_elem(60)), mul_(a, c), mul_(mod_(add_(as_elem(93), mul_(mul_(mul_(c, b), mul_(a, c)), m)), m), as_elem(60)), mul_(a, c));
		cong_mul_(mod_(as_elem(93), m), as_elem(60), mod_(add_(as_elem(93), mul_(mul_(mul_(c, b), mul_(a, c)), m)), m), as_elem(60));
		lemma_eq_ref(mul_(a, c));
		lemma_eq_ref(as_elem(60));
	}
	let temp_89_0 = (add_((mul_(b, (mod_(a, m)))), (mul_(a, b))));
	let temp_89_1 = (add_((mul_(b, (mod_(a, m)))), (mul_(b, a))));
	assert(eq_(temp_89_0, temp_89_1)) by {
		cong_add_(mul_(b, mod_(a, m)), mul_(a, b), mul_(b, mod_(a, m)), mul_(b, a));
		lemma_mul_comm(a, b);
		lemma_eq_ref(mul_(b, mod_(a, m)));
	}
	let temp_90_0 = (mul_((add_((mod_(c, m)), a)), (mul_(d, a))));
	let temp_90_1 = (add_((mul_((mod_(c, m)), (mul_(d, a)))), (mul_(a, (mul_(d, a))))));
	assert(eq_(temp_90_0, temp_90_1)) by {
		lemma_mul_dist(mod_(c, m), a, mul_(d, a));
	}
	let temp_91_0 = (mul_((mul_(c, b)), (add_(c, d))));
	let temp_91_1 = (mul_((add_(c, d)), (mul_(c, b))));
	assert(eq_(temp_91_0, temp_91_1)) by {
		lemma_mul_comm(mul_(c, b), add_(c, d));
	}
	let temp_92_0 = (mul_((mul_(c, b)), (mul_(b, a))));
	let temp_92_1 = (mul_((mul_(b, c)), (mul_(b, a))));
	assert(eq_(temp_92_0, temp_92_1)) by {
		lemma_eq_ref(mul_(b, a));
		cong_mul_(mul_(c, b), mul_(b, a), mul_(b, c), mul_(b, a));
		lemma_mul_comm(c, b);
	}
	let temp_93_0 = (mul_((add_(d, d)), (mod_((mul_(b, a)), m))));
	let temp_93_1 = (add_((mul_(d, (mod_((mul_(b, a)), m)))), (mul_(d, (mod_((mul_(b, a)), m))))));
	assert(eq_(temp_93_0, temp_93_1)) by {
		lemma_mul_dist(d, d, mod_(mul_(b, a), m));
	}
	let temp_94_0 = (mul_((add_(d, b)), (mul_(d, b))));
	let temp_94_1 = (mul_((add_(b, d)), (mul_(d, b))));
	assert(eq_(temp_94_0, temp_94_1)) by {
		cong_mul_(add_(d, b), mul_(d, b), add_(b, d), mul_(d, b));
		lemma_add_comm(d, b);
		lemma_eq_ref(mul_(d, b));
	}
	let temp_95_0 = (mod_((mul_((mul_(c, c)), (mul_(c, c)))), m));
	let temp_95_1 = (mod_((add_((mul_((mul_(c, c)), (mul_(c, c)))), (mul_((add_(d, (mul_(b, d)))), m)))), m));
	assert(eq_(temp_95_0, temp_95_1)) by {
		lemma_mod_mul_vanish(mul_(mul_(c, c), mul_(c, c)), add_(d, mul_(b, d)), m);
	}
	let temp_96_0 = (sub_((mul_(a, d)), (mul_(as_elem(76), a))));
	let temp_96_1 = (sub_((mul_(d, a)), (mul_(as_elem(76), a))));
	assert(eq_(temp_96_0, temp_96_1)) by {
		cong_sub_(mul_(a, d), mul_(as_elem(76), a), mul_(d, a), mul_(as_elem(76), a));
		lemma_mul_comm(a, d);
		lemma_eq_ref(mul_(as_elem(76), a));
	}
	let temp_97_0 = (sub_((mul_(a, (mod_(b, m)))), (mul_(d, (mod_(a, m))))));
	let temp_97_1 = (sub_((mul_(a, (mod_((add_(b, (mul_((sub_((mul_(c, a)), (mul_(b, d)))), m)))), m)))), (mul_(d, (mod_(a, m))))));
	assert(eq_(temp_97_0, temp_97_1)) by {
		cong_mul_(a, mod_(b, m), a, mod_(add_(b, mul_(sub_(mul_(c, a), mul_(b, d)), m)), m));
		lemma_eq_ref(a);
		lemma_eq_ref(mul_(d, mod_(a, m)));
		lemma_mod_mul_vanish(b, sub_(mul_(c, a), mul_(b, d)), m);
		cong_sub_(mul_(a, mod_(b, m)), mul_(d, mod_(a, m)), mul_(a, mod_(add_(b, mul_(sub_(mul_(c, a), mul_(b, d)), m)), m)), mul_(d, mod_(a, m)));
	}
	let temp_98_0 = (mod_((mul_((mul_(a, b)), (add_(c, as_elem(35))))), m));
	let temp_98_1 = (mod_((add_((mul_((mul_(a, b)), c)), (mul_((mul_(a, b)), as_elem(35))))), m));
	assert(eq_(temp_98_0, temp_98_1)) by {
		lemma_mul_dist(mul_(a, b), c, as_elem(35));
		cong_mod_(mul_(mul_(a, b), add_(c, as_elem(35))), m, add_(mul_(mul_(a, b), c), mul_(mul_(a, b), as_elem(35))), m);
		lemma_eq_ref(m);
	}
	let temp_99_0 = (mul_((sub_(b, a)), (mul_(d, d))));
	let temp_99_1 = (mul_((mul_(d, d)), (sub_(b, a))));
	assert(eq_(temp_99_0, temp_99_1)) by {
		lemma_mul_comm(sub_(b, a), mul_(d, d));
	}
	let temp_100_0 = (mul_((mul_(b, a)), (mul_((mod_(b, m)), d))));
	let temp_100_1 = (mul_((mul_(b, a)), (mul_((mod_((add_((mul_((mul_((mul_(c, c)), (mul_(c, c)))), m)), b)), m)), d))));
	assert(eq_(temp_100_0, temp_100_1)) by {
		lemma_mod_mul_vanish(b, mul_(mul_(c, c), mul_(c, c)), m);
		cong_mul_(mul_(b, a), mul_(mod_(b, m), d), mul_(b, a), mul_(mod_(add_(mul_(mul_(mul_(c, c), mul_(c, c)), m), b), m), d));
		lemma_eq_ref(d);
		lemma_eq_ref(mul_(b, a));
		cong_mul_(mod_(b, m), d, mod_(add_(mul_(mul_(mul_(c, c), mul_(c, c)), m), b), m), d);
	}
	let temp_101_0 = (mul_((mod_((mul_(d, c)), m)), (mul_(d, d))));
	let temp_101_1 = (mul_((mul_((mod_((mul_(d, c)), m)), d)), d));
	assert(eq_(temp_101_0, temp_101_1)) by {
		lemma_mul_assoc(mod_(mul_(d, c), m), d, d);
	}
	let temp_102_0 = (mul_((add_(a, c)), (mul_(b, d))));
	let temp_102_1 = (mul_((add_(c, a)), (mul_(b, d))));
	assert(eq_(temp_102_0, temp_102_1)) by {
		lemma_add_comm(a, c);
		cong_mul_(add_(a, c), mul_(b, d), add_(c, a), mul_(b, d));
		lemma_eq_ref(mul_(b, d));
	}
	let temp_103_0 = (mul_((add_((mod_(a, m)), d)), (mul_(c, c))));
	let temp_103_1 = (mul_((add_(d, (mod_(a, m)))), (mul_(c, c))));
	assert(eq_(temp_103_0, temp_103_1)) by {
		lemma_mul_comm(c, c);
		lemma_add_comm(mod_(a, m), d);
		cong_mul_(add_(mod_(a, m), d), mul_(c, c), add_(d, mod_(a, m)), mul_(c, c));
	}
	let temp_104_0 = (mul_((mul_(c, d)), (mod_((mul_((mod_(a, m)), b)), m))));
	let temp_104_1 = (mul_(c, (mul_(d, (mod_((mul_((mod_(a, m)), b)), m))))));
	assert(eq_(temp_104_0, temp_104_1)) by {
		lemma_mul_assoc(c, d, mod_(mul_(mod_(a, m), b), m));
		lemma_eq_sym(temp_104_1, temp_104_0);
	}

}

} // verus!