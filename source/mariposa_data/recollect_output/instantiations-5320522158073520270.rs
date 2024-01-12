use builtin_macros::*;
// use builtin::*;
mod nl_basics;
use crate::nl_basics::*;
verus! {

pub proof fn free_0(a: Elem, b: Elem, c: Elem, d: Elem, m: Elem)
{
	let temp_0_0 = (mul_((mul_(d, b)), (mul_(d, c))));
	let temp_0_1 = (mul_((mul_(b, d)), (mul_(d, c))));
	assert(eq_(temp_0_0, temp_0_1)) by {
		cong_mul_(mul_(d, b), mul_(d, c), mul_(b, d), mul_(d, c));
		lemma_mul_comm(d, b);
		lemma_eq_ref(mul_(d, c));
	}
	let temp_1_0 = (mul_((mul_(a, c)), (mul_(a, b))));
	let temp_1_1 = (mul_(a, (mul_(c, (mul_(a, b))))));
	assert(eq_(temp_1_0, temp_1_1)) by {
		lemma_eq_sym(temp_1_1, temp_1_0);
		lemma_mul_assoc(a, c, mul_(a, b));
	}
	let temp_2_0 = (mul_((mul_(d, a)), (mul_(b, d))));
	let temp_2_1 = (mul_((mul_(b, d)), (mul_(d, a))));
	assert(eq_(temp_2_0, temp_2_1)) by {
		lemma_mul_comm(mul_(d, a), mul_(b, d));
	}
	let temp_3_0 = (sub_((mul_((mod_(d, m)), d)), (add_(c, c))));
	let temp_3_1 = (sub_((mul_(d, (mod_(d, m)))), (add_(c, c))));
	assert(eq_(temp_3_0, temp_3_1)) by {
		cong_sub_(mul_(mod_(d, m), d), add_(c, c), mul_(d, mod_(d, m)), add_(c, c));
		lemma_mul_comm(mod_(d, m), d);
		lemma_eq_ref(add_(c, c));
	}
	let temp_4_0 = (mul_((mod_((mul_(b, c)), m)), (mod_((add_(a, (mod_(c, m)))), m))));
	let temp_4_1 = (mul_((mod_((mul_(b, c)), m)), (mod_((add_((mod_(a, m)), (mod_(c, m)))), m))));
	assert(eq_(temp_4_0, temp_4_1)) by {
		lemma_mod_add_noop(a, mod_(c, m), m);
		cong_mul_(mod_(mul_(b, c), m), mod_(add_(a, mod_(c, m)), m), mod_(mul_(b, c), m), mod_(add_(mod_(a, m), mod_(c, m)), m));
		lemma_eq_ref(mod_(mul_(b, c), m));
	}
	let temp_5_0 = (mul_((mul_(b, a)), (mul_(a, c))));
	let temp_5_1 = (mul_((mul_(a, c)), (mul_(b, a))));
	assert(eq_(temp_5_0, temp_5_1)) by {
		lemma_mul_comm(mul_(b, a), mul_(a, c));
	}
	let temp_6_0 = (mod_((mul_((mod_((add_(b, c)), m)), (mul_(a, d)))), m));
	let temp_6_1 = (mod_((mul_((mod_((add_(b, c)), m)), (mul_(d, a)))), m));
	assert(eq_(temp_6_0, temp_6_1)) by {
		lemma_mul_comm(a, d);
		cong_mod_(mul_(mod_(add_(b, c), m), mul_(a, d)), m, mul_(mod_(add_(b, c), m), mul_(d, a)), m);
		lemma_eq_ref(mod_(add_(b, c), m));
		cong_mul_(mod_(add_(b, c), m), mul_(a, d), mod_(add_(b, c), m), mul_(d, a));
		lemma_eq_ref(m);
	}
	let temp_7_0 = (sub_((mul_((mod_(d, m)), a)), (mul_(d, a))));
	let temp_7_1 = (mul_((sub_((mod_(d, m)), d)), a));
	assert(eq_(temp_7_0, temp_7_1)) by {
		lemma_eq_sym(temp_7_1, temp_7_0);
		lemma_mul_dist(a, mod_(d, m), d);
	}
	let temp_8_0 = (mul_((mul_(a, a)), (mul_(b, b))));
	let temp_8_1 = (mul_((mul_(a, a)), (mul_(b, b))));
	assert(eq_(temp_8_0, temp_8_1)) by {
		lemma_eq_ref(temp_8_0);
	}
	let temp_9_0 = (add_((mul_(c, a)), (mul_(d, a))));
	let temp_9_1 = (mul_((add_(c, d)), a));
	assert(eq_(temp_9_0, temp_9_1)) by {
		lemma_eq_sym(temp_9_1, temp_9_0);
		lemma_mul_dist(c, d, a);
	}
	let temp_10_0 = (mul_((mul_((mod_(c, m)), b)), (mod_((mul_(c, b)), m))));
	let temp_10_1 = (mul_((mul_((mod_((sub_(c, (mul_((sub_((mul_(d, d)), (mul_(b, b)))), m)))), m)), b)), (mod_((mul_(c, b)), m))));
	assert(eq_(temp_10_0, temp_10_1)) by {
		lemma_mod_mul_vanish(c, sub_(mul_(d, d), mul_(b, b)), m);
		cong_mul_(mul_(mod_(c, m), b), mod_(mul_(c, b), m), mul_(mod_(sub_(c, mul_(sub_(mul_(d, d), mul_(b, b)), m)), m), b), mod_(mul_(c, b), m));
		lemma_eq_ref(b);
		cong_mul_(mod_(c, m), b, mod_(sub_(c, mul_(sub_(mul_(d, d), mul_(b, b)), m)), m), b);
		lemma_eq_ref(mod_(mul_(c, b), m));
	}
	let temp_11_0 = (mul_((mod_((mul_(b, b)), m)), (mul_(c, d))));
	let temp_11_1 = (mul_((mod_((mul_(b, b)), m)), (mul_(d, c))));
	assert(eq_(temp_11_0, temp_11_1)) by {
		lemma_mul_comm(c, d);
		cong_mul_(mod_(mul_(b, b), m), mul_(c, d), mod_(mul_(b, b), m), mul_(d, c));
		lemma_eq_ref(mod_(mul_(b, b), m));
	}
	let temp_12_0 = (add_((mul_(b, a)), (mul_(b, a))));
	let temp_12_1 = (add_((mul_(b, a)), (mul_(b, a))));
	assert(eq_(temp_12_0, temp_12_1)) by {
		lemma_eq_ref(temp_12_0);
	}
	let temp_13_0 = (sub_((mul_(b, d)), (mul_(b, a))));
	let temp_13_1 = (sub_((mul_(d, b)), (mul_(b, a))));
	assert(eq_(temp_13_0, temp_13_1)) by {
		cong_sub_(mul_(b, d), mul_(b, a), mul_(d, b), mul_(b, a));
		lemma_mul_comm(b, d);
		lemma_eq_ref(mul_(b, a));
	}
	let temp_14_0 = (mul_((mul_(c, c)), (sub_(a, c))));
	let temp_14_1 = (mul_((sub_(a, c)), (mul_(c, c))));
	assert(eq_(temp_14_0, temp_14_1)) by {
		lemma_mul_comm(mul_(c, c), sub_(a, c));
	}
	let temp_15_0 = (mul_((mul_(c, (mod_(b, m)))), (add_(d, (mod_(b, m))))));
	let temp_15_1 = (mul_((mul_(c, (mod_(b, m)))), (add_((mod_(b, m)), d))));
	assert(eq_(temp_15_0, temp_15_1)) by {
		lemma_add_comm(d, mod_(b, m));
		cong_mul_(mul_(c, mod_(b, m)), add_(d, mod_(b, m)), mul_(c, mod_(b, m)), add_(mod_(b, m), d));
		lemma_eq_ref(mul_(c, mod_(b, m)));
	}
	let temp_16_0 = (mul_((mul_(c, c)), (sub_(c, c))));
	let temp_16_1 = (mul_(c, (mul_(c, (sub_(c, c))))));
	assert(eq_(temp_16_0, temp_16_1)) by {
		lemma_eq_sym(temp_16_1, temp_16_0);
		lemma_mul_assoc(c, c, sub_(c, c));
	}
	let temp_17_0 = (mul_((sub_(b, d)), (add_(c, as_elem(68)))));
	let temp_17_1 = (mul_((sub_(b, d)), (add_(as_elem(68), c))));
	assert(eq_(temp_17_0, temp_17_1)) by {
		lemma_add_comm(c, as_elem(68));
		cong_mul_(sub_(b, d), add_(c, as_elem(68)), sub_(b, d), add_(as_elem(68), c));
		lemma_eq_ref(sub_(b, d));
	}
	let temp_18_0 = (mul_((sub_(a, a)), (mul_(b, c))));
	let temp_18_1 = (sub_((mul_(a, (mul_(b, c)))), (mul_(a, (mul_(b, c))))));
	assert(eq_(temp_18_0, temp_18_1)) by {
		lemma_mul_dist(mul_(b, c), a, a);
	}
	let temp_19_0 = (mul_((mul_(d, (mod_(c, m)))), (mul_(d, a))));
	let temp_19_1 = (mul_((mul_(d, (mod_((sub_(c, (mul_((add_((mul_((mod_(d, m)), d)), (sub_(b, b)))), m)))), m)))), (mul_(d, a))));
	assert(eq_(temp_19_0, temp_19_1)) by {
		lemma_mod_mul_vanish(c, add_(mul_(mod_(d, m), d), sub_(b, b)), m);
		cong_mul_(mul_(d, mod_(c, m)), mul_(d, a), mul_(d, mod_(sub_(c, mul_(add_(mul_(mod_(d, m), d), sub_(b, b)), m)), m)), mul_(d, a));
		lemma_eq_ref(d);
		cong_mul_(d, mod_(c, m), d, mod_(sub_(c, mul_(add_(mul_(mod_(d, m), d), sub_(b, b)), m)), m));
		lemma_eq_ref(mul_(d, a));
	}
	let temp_20_0 = (mul_((mul_((mod_(c, m)), b)), (mul_((mod_(c, m)), c))));
	let temp_20_1 = (mul_((mul_((mod_((add_(c, (mul_((mul_((mul_(d, b)), (mul_(c, c)))), m)))), m)), b)), (mul_((mod_(c, m)), c))));
	assert(eq_(temp_20_0, temp_20_1)) by {
		lemma_mod_mul_vanish(c, mul_(mul_(d, b), mul_(c, c)), m);
		cong_mul_(mul_(mod_(c, m), b), mul_(mod_(c, m), c), mul_(mod_(add_(c, mul_(mul_(mul_(d, b), mul_(c, c)), m)), m), b), mul_(mod_(c, m), c));
		lemma_eq_ref(b);
		cong_mul_(mod_(c, m), b, mod_(add_(c, mul_(mul_(mul_(d, b), mul_(c, c)), m)), m), b);
		lemma_eq_ref(mul_(mod_(c, m), c));
	}
	let temp_21_0 = (sub_((mul_(d, c)), (mod_((mul_((mod_(d, m)), as_elem(73))), m))));
	let temp_21_1 = (sub_((mul_(c, d)), (mod_((mul_((mod_(d, m)), as_elem(73))), m))));
	assert(eq_(temp_21_0, temp_21_1)) by {
		lemma_mul_comm(d, c);
		cong_sub_(mul_(d, c), mod_(mul_(mod_(d, m), as_elem(73)), m), mul_(c, d), mod_(mul_(mod_(d, m), as_elem(73)), m));
		lemma_eq_ref(mod_(mul_(mod_(d, m), as_elem(73)), m));
	}
	let temp_22_0 = (add_((mod_((mul_(d, d)), m)), (mul_(a, a))));
	let temp_22_1 = (add_((mod_((add_((mul_((mul_((mul_(d, a)), (mul_(b, b)))), m)), (mul_(d, d)))), m)), (mul_(a, a))));
	assert(eq_(temp_22_0, temp_22_1)) by {
		lemma_mod_mul_vanish(mul_(d, d), mul_(mul_(d, a), mul_(b, b)), m);
		cong_add_(mod_(mul_(d, d), m), mul_(a, a), mod_(add_(mul_(mul_(mul_(d, a), mul_(b, b)), m), mul_(d, d)), m), mul_(a, a));
		lemma_eq_ref(mul_(a, a));
	}
	let temp_23_0 = (mul_((mul_(c, d)), (mul_((mod_(b, m)), d))));
	let temp_23_1 = (mul_((mul_(d, c)), (mul_((mod_(b, m)), d))));
	assert(eq_(temp_23_0, temp_23_1)) by {
		lemma_mul_comm(c, d);
		cong_mul_(mul_(c, d), mul_(mod_(b, m), d), mul_(d, c), mul_(mod_(b, m), d));
		lemma_eq_ref(mul_(mod_(b, m), d));
	}
	let temp_24_0 = (mul_((mul_(d, d)), (mod_((mul_(c, b)), m))));
	let temp_24_1 = (mul_((mul_(d, d)), (mod_((add_((mul_((mul_((mul_((mod_(b, m)), as_elem(70))), (mul_(a, as_elem(49))))), m)), (mul_(c, b)))), m))));
	assert(eq_(temp_24_0, temp_24_1)) by {
		cong_mul_(mul_(d, d), mod_(mul_(c, b), m), mul_(d, d), mod_(add_(mul_(mul_(mul_(mod_(b, m), as_elem(70)), mul_(a, as_elem(49))), m), mul_(c, b)), m));
		lemma_mod_mul_vanish(mul_(c, b), mul_(mul_(mod_(b, m), as_elem(70)), mul_(a, as_elem(49))), m);
		lemma_eq_ref(mul_(d, d));
	}
	let temp_25_0 = (mul_((mul_(a, a)), (mul_(a, b))));
	let temp_25_1 = (mul_((mul_(a, a)), (mul_(a, b))));
	assert(eq_(temp_25_0, temp_25_1)) by {
		lemma_eq_ref(temp_25_0);
	}
	let temp_26_0 = (mul_((sub_(b, b)), (mul_((mod_(d, m)), a))));
	let temp_26_1 = (mul_((sub_(b, b)), (mul_((mod_((add_((mul_((mul_((mul_(a, c)), (mul_(a, c)))), m)), d)), m)), a))));
	assert(eq_(temp_26_0, temp_26_1)) by {
		lemma_mod_mul_vanish(d, mul_(mul_(a, c), mul_(a, c)), m);
		cong_mul_(sub_(b, b), mul_(mod_(d, m), a), sub_(b, b), mul_(mod_(add_(mul_(mul_(mul_(a, c), mul_(a, c)), m), d), m), a));
		lemma_eq_ref(a);
		cong_mul_(mod_(d, m), a, mod_(add_(mul_(mul_(mul_(a, c), mul_(a, c)), m), d), m), a);
		lemma_eq_ref(sub_(b, b));
	}
	let temp_27_0 = (mul_((mul_(d, (mod_(d, m)))), (mul_(b, d))));
	let temp_27_1 = (mul_((mul_((mul_(d, (mod_(d, m)))), b)), d));
	assert(eq_(temp_27_0, temp_27_1)) by {
		lemma_mul_assoc(mul_(d, mod_(d, m)), b, d);
	}
	let temp_28_0 = (mul_((mul_(b, as_elem(58))), (mul_(b, a))));
	let temp_28_1 = (mul_((mul_(b, as_elem(58))), (mul_(a, b))));
	assert(eq_(temp_28_0, temp_28_1)) by {
		cong_mul_(mul_(b, as_elem(58)), mul_(b, a), mul_(b, as_elem(58)), mul_(a, b));
		lemma_mul_comm(b, a);
		lemma_eq_ref(mul_(b, as_elem(58)));
	}
	let temp_29_0 = (sub_((mul_(d, d)), (mul_(d, c))));
	let temp_29_1 = (sub_((mul_(d, d)), (mul_(c, d))));
	assert(eq_(temp_29_0, temp_29_1)) by {
		cong_sub_(mul_(d, d), mul_(d, c), mul_(d, d), mul_(c, d));
		lemma_mul_comm(d, d);
		lemma_mul_comm(d, c);
	}
	let temp_30_0 = (sub_((mul_(a, (mod_(d, m)))), (mod_((mul_(b, c)), m))));
	let temp_30_1 = (sub_((mul_((mod_(d, m)), a)), (mod_((mul_(b, c)), m))));
	assert(eq_(temp_30_0, temp_30_1)) by {
		lemma_mul_comm(a, mod_(d, m));
		cong_sub_(mul_(a, mod_(d, m)), mod_(mul_(b, c), m), mul_(mod_(d, m), a), mod_(mul_(b, c), m));
		lemma_eq_ref(mod_(mul_(b, c), m));
	}
	let temp_31_0 = (mul_((mod_((mul_(d, as_elem(66))), m)), (mod_((mul_(a, c)), m))));
	let temp_31_1 = (mul_((mod_((mul_(d, as_elem(66))), m)), (mod_((sub_((mul_(a, c)), (mul_((mul_(a, (mul_(c, d)))), m)))), m))));
	assert(eq_(temp_31_0, temp_31_1)) by {
		lemma_mod_mul_vanish(mul_(a, c), mul_(a, mul_(c, d)), m);
		cong_mul_(mod_(mul_(d, as_elem(66)), m), mod_(mul_(a, c), m), mod_(mul_(d, as_elem(66)), m), mod_(sub_(mul_(a, c), mul_(mul_(a, mul_(c, d)), m)), m));
		lemma_eq_ref(mod_(mul_(d, as_elem(66)), m));
	}
	let temp_32_0 = (mul_((mod_((mul_(b, a)), m)), (mul_(c, a))));
	let temp_32_1 = (mul_((mod_((add_((mul_(b, a)), (mul_((mul_((mul_(a, d)), (mul_(d, c)))), m)))), m)), (mul_(c, a))));
	assert(eq_(temp_32_0, temp_32_1)) by {
		lemma_mod_mul_vanish(mul_(b, a), mul_(mul_(a, d), mul_(d, c)), m);
		cong_mul_(mod_(mul_(b, a), m), mul_(c, a), mod_(add_(mul_(b, a), mul_(mul_(mul_(a, d), mul_(d, c)), m)), m), mul_(c, a));
		lemma_eq_ref(mul_(c, a));
	}
	let temp_33_0 = (sub_((mod_((mul_(d, b)), m)), (mul_(c, a))));
	let temp_33_1 = (sub_((mod_((mul_(b, d)), m)), (mul_(c, a))));
	assert(eq_(temp_33_0, temp_33_1)) by {
		lemma_mul_comm(d, b);
		cong_sub_(mod_(mul_(d, b), m), mul_(c, a), mod_(mul_(b, d), m), mul_(c, a));
		cong_mod_(mul_(d, b), m, mul_(b, d), m);
		lemma_eq_ref(mul_(c, a));
		lemma_eq_ref(m);
	}
	let temp_34_0 = (mul_((mul_(d, a)), (mul_(a, a))));
	let temp_34_1 = (mul_((mul_((mul_(d, a)), a)), a));
	assert(eq_(temp_34_0, temp_34_1)) by {
		lemma_mul_assoc(mul_(d, a), a, a);
	}
	let temp_35_0 = (mul_((mul_(c, (mod_(b, m)))), (mul_(a, c))));
	let temp_35_1 = (mul_((mul_(c, (mod_(b, m)))), (mul_(c, a))));
	assert(eq_(temp_35_0, temp_35_1)) by {
		lemma_mul_comm(a, c);
		cong_mul_(mul_(c, mod_(b, m)), mul_(a, c), mul_(c, mod_(b, m)), mul_(c, a));
		lemma_eq_ref(mul_(c, mod_(b, m)));
	}
	let temp_36_0 = (mul_((mul_(d, c)), (mul_(d, c))));
	let temp_36_1 = (mul_((mul_((mul_(d, c)), d)), c));
	assert(eq_(temp_36_0, temp_36_1)) by {
		lemma_mul_assoc(mul_(d, c), d, c);
	}
	let temp_37_0 = (sub_((add_(d, b)), (mul_(c, d))));
	let temp_37_1 = (sub_((add_(b, d)), (mul_(c, d))));
	assert(eq_(temp_37_0, temp_37_1)) by {
		cong_sub_(add_(d, b), mul_(c, d), add_(b, d), mul_(c, d));
		lemma_add_comm(d, b);
		lemma_eq_ref(mul_(c, d));
	}
	let temp_38_0 = (mul_((sub_(d, c)), (mul_(c, a))));
	let temp_38_1 = (mul_((mul_(c, a)), (sub_(d, c))));
	assert(eq_(temp_38_0, temp_38_1)) by {
		lemma_mul_comm(sub_(d, c), mul_(c, a));
	}
	let temp_39_0 = (mod_((mul_((mul_(c, d)), (mul_(b, d)))), m));
	let temp_39_1 = (mod_((sub_((mul_((mul_(c, d)), (mul_(b, d)))), (mul_((mul_((mul_(a, c)), (mul_(b, (mod_(b, m)))))), m)))), m));
	assert(eq_(temp_39_0, temp_39_1)) by {
		lemma_mod_mul_vanish(mul_(mul_(c, d), mul_(b, d)), mul_(mul_(a, c), mul_(b, mod_(b, m))), m);
	}
	let temp_40_0 = (mul_((mul_(b, c)), (mul_(d, c))));
	let temp_40_1 = (mul_(b, (mul_(c, (mul_(d, c))))));
	assert(eq_(temp_40_0, temp_40_1)) by {
		lemma_eq_sym(temp_40_1, temp_40_0);
		lemma_mul_assoc(b, c, mul_(d, c));
	}
	let temp_41_0 = (sub_((sub_(c, c)), (mul_(as_elem(77), c))));
	let temp_41_1 = (sub_((sub_(c, c)), (mul_(c, as_elem(77)))));
	assert(eq_(temp_41_0, temp_41_1)) by {
		cong_sub_(sub_(c, c), mul_(as_elem(77), c), sub_(c, c), mul_(c, as_elem(77)));
		lemma_mul_comm(as_elem(77), c);
		cong_sub_(c, c, c, c);
		lemma_eq_ref(c);
	}
	let temp_42_0 = (mul_((mul_(c, (mod_(a, m)))), (mul_(c, b))));
	let temp_42_1 = (mul_((mul_(c, (mod_((sub_(a, (mul_((mul_((mul_(c, d)), (mul_(d, d)))), m)))), m)))), (mul_(c, b))));
	assert(eq_(temp_42_0, temp_42_1)) by {
		lemma_mod_mul_vanish(a, mul_(mul_(c, d), mul_(d, d)), m);
		cong_mul_(mul_(c, mod_(a, m)), mul_(c, b), mul_(c, mod_(sub_(a, mul_(mul_(mul_(c, d), mul_(d, d)), m)), m)), mul_(c, b));
		lemma_eq_ref(c);
		cong_mul_(c, mod_(a, m), c, mod_(sub_(a, mul_(mul_(mul_(c, d), mul_(d, d)), m)), m));
		lemma_eq_ref(mul_(c, b));
	}
	let temp_43_0 = (sub_((sub_(c, b)), (mul_((mod_(b, m)), (mod_(c, m))))));
	let temp_43_1 = (sub_((sub_(c, b)), (mul_((mod_(c, m)), (mod_(b, m))))));
	assert(eq_(temp_43_0, temp_43_1)) by {
		lemma_mul_comm(mod_(b, m), mod_(c, m));
		cong_sub_(sub_(c, b), mul_(mod_(b, m), mod_(c, m)), sub_(c, b), mul_(mod_(c, m), mod_(b, m)));
		lemma_eq_ref(sub_(c, b));
	}
	let temp_44_0 = (mul_((mod_((mul_(b, d)), m)), (mul_((mod_(a, m)), a))));
	let temp_44_1 = (mul_((mul_((mod_(a, m)), a)), (mod_((mul_(b, d)), m))));
	assert(eq_(temp_44_0, temp_44_1)) by {
		lemma_mul_comm(mod_(mul_(b, d), m), mul_(mod_(a, m), a));
	}
	let temp_45_0 = (mul_((mul_(d, a)), (sub_((mod_(d, m)), b))));
	let temp_45_1 = (mul_((mul_(d, a)), (sub_((mod_((add_((mul_((mul_((mod_((sub_(b, d)), m)), (mul_((mod_(d, m)), d)))), m)), d)), m)), b))));
	assert(eq_(temp_45_0, temp_45_1)) by {
		lemma_mod_mul_vanish(d, mul_(mod_(sub_(b, d), m), mul_(mod_(d, m), d)), m);
		cong_mul_(mul_(d, a), sub_(mod_(d, m), b), mul_(d, a), sub_(mod_(add_(mul_(mul_(mod_(sub_(b, d), m), mul_(mod_(d, m), d)), m), d), m), b));
		cong_sub_(mod_(d, m), b, mod_(add_(mul_(mul_(mod_(sub_(b, d), m), mul_(mod_(d, m), d)), m), d), m), b);
		lemma_eq_ref(mul_(d, a));
		lemma_eq_ref(b);
	}
	let temp_46_0 = (sub_((mul_(d, a)), (mul_(a, (mod_(b, m))))));
	let temp_46_1 = (sub_((mul_(a, d)), (mul_(a, (mod_(b, m))))));
	assert(eq_(temp_46_0, temp_46_1)) by {
		lemma_mul_comm(d, a);
		cong_sub_(mul_(d, a), mul_(a, mod_(b, m)), mul_(a, d), mul_(a, mod_(b, m)));
		lemma_eq_ref(mul_(a, mod_(b, m)));
	}
	let temp_47_0 = (mul_((mul_(b, b)), (mul_((mod_(a, m)), c))));
	let temp_47_1 = (mul_((mul_(b, b)), (mul_((mod_((add_(a, (mul_((sub_((mul_(d, d)), (mul_(b, a)))), m)))), m)), c))));
	assert(eq_(temp_47_0, temp_47_1)) by {
		lemma_mul_comm(b, b);
		lemma_mod_mul_vanish(a, sub_(mul_(d, d), mul_(b, a)), m);
		cong_mul_(mul_(b, b), mul_(mod_(a, m), c), mul_(b, b), mul_(mod_(add_(a, mul_(sub_(mul_(d, d), mul_(b, a)), m)), m), c));
		cong_mul_(mod_(a, m), c, mod_(add_(a, mul_(sub_(mul_(d, d), mul_(b, a)), m)), m), c);
		lemma_eq_ref(c);
	}
	let temp_48_0 = (sub_((add_(d, b)), (mul_(b, c))));
	let temp_48_1 = (sub_((add_(d, b)), (mul_(c, b))));
	assert(eq_(temp_48_0, temp_48_1)) by {
		cong_sub_(add_(d, b), mul_(b, c), add_(d, b), mul_(c, b));
		lemma_mul_comm(b, c);
		lemma_eq_ref(add_(d, b));
	}
	let temp_49_0 = (mul_((mul_(a, as_elem(19))), (mod_((mul_(c, a)), m))));
	let temp_49_1 = (mul_((mul_(a, as_elem(19))), (mod_((mul_(a, c)), m))));
	assert(eq_(temp_49_0, temp_49_1)) by {
		lemma_mul_comm(c, a);
		cong_mul_(mul_(a, as_elem(19)), mod_(mul_(c, a), m), mul_(a, as_elem(19)), mod_(mul_(a, c), m));
		lemma_eq_ref(m);
		lemma_eq_ref(mul_(a, as_elem(19)));
		cong_mod_(mul_(c, a), m, mul_(a, c), m);
	}
	let temp_50_0 = (mul_((mul_(b, c)), (mul_(a, d))));
	let temp_50_1 = (mul_((mul_(b, c)), (mul_(d, a))));
	assert(eq_(temp_50_0, temp_50_1)) by {
		cong_mul_(mul_(b, c), mul_(a, d), mul_(b, c), mul_(d, a));
		lemma_mul_comm(a, d);
		lemma_eq_ref(mul_(b, c));
	}
	let temp_51_0 = (mod_((add_((mod_((mul_(a, c)), m)), (mod_((mul_(a, a)), m)))), m));
	let temp_51_1 = (mod_((add_((mod_((mul_(a, a)), m)), (mod_((mul_(a, c)), m)))), m));
	assert(eq_(temp_51_0, temp_51_1)) by {
		lemma_add_comm(mod_(mul_(a, c), m), mod_(mul_(a, a), m));
		cong_mod_(add_(mod_(mul_(a, c), m), mod_(mul_(a, a), m)), m, add_(mod_(mul_(a, a), m), mod_(mul_(a, c), m)), m);
		lemma_eq_ref(m);
	}
	let temp_52_0 = (mul_((mul_((mod_(d, m)), c)), (mul_(a, c))));
	let temp_52_1 = (mul_((mod_(d, m)), (mul_(c, (mul_(a, c))))));
	assert(eq_(temp_52_0, temp_52_1)) by {
		lemma_mul_assoc(mod_(d, m), c, mul_(a, c));
		lemma_eq_sym(temp_52_1, temp_52_0);
	}
	let temp_53_0 = (mul_((mul_(c, d)), (add_(b, a))));
	let temp_53_1 = (add_((mul_((mul_(c, d)), b)), (mul_((mul_(c, d)), a))));
	assert(eq_(temp_53_0, temp_53_1)) by {
		lemma_mul_dist(mul_(c, d), b, a);
	}
	let temp_54_0 = (mul_((mul_(b, c)), (add_((mod_(b, m)), a))));
	let temp_54_1 = (mul_((mul_(b, c)), (add_(a, (mod_(b, m))))));
	assert(eq_(temp_54_0, temp_54_1)) by {
		lemma_add_comm(mod_(b, m), a);
		cong_mul_(mul_(b, c), add_(mod_(b, m), a), mul_(b, c), add_(a, mod_(b, m)));
		lemma_eq_ref(mul_(b, c));
	}
	let temp_55_0 = (mul_((mul_(c, c)), (add_(c, d))));
	let temp_55_1 = (add_((mul_((mul_(c, c)), c)), (mul_((mul_(c, c)), d))));
	assert(eq_(temp_55_0, temp_55_1)) by {
		lemma_mul_dist(mul_(c, c), c, d);
	}
	let temp_56_0 = (mul_((mul_(d, d)), (sub_((mod_(d, m)), d))));
	let temp_56_1 = (mul_((mul_(d, d)), (sub_((mod_((add_(d, (mul_((mul_((mod_((mul_(c, a)), m)), (mul_(a, c)))), m)))), m)), d))));
	assert(eq_(temp_56_0, temp_56_1)) by {
		lemma_mul_comm(d, d);
		lemma_mod_mul_vanish(d, mul_(mod_(mul_(c, a), m), mul_(a, c)), m);
		cong_mul_(mul_(d, d), sub_(mod_(d, m), d), mul_(d, d), sub_(mod_(add_(d, mul_(mul_(mod_(mul_(c, a), m), mul_(a, c)), m)), m), d));
		cong_sub_(mod_(d, m), d, mod_(add_(d, mul_(mul_(mod_(mul_(c, a), m), mul_(a, c)), m)), m), d);
		lemma_eq_ref(d);
	}
	let temp_57_0 = (sub_((mul_(d, d)), (mul_(a, c))));
	let temp_57_1 = (sub_((mul_(d, d)), (mul_(c, a))));
	assert(eq_(temp_57_0, temp_57_1)) by {
		cong_sub_(mul_(d, d), mul_(a, c), mul_(d, d), mul_(c, a));
		lemma_mul_comm(a, c);
		lemma_eq_ref(mul_(d, d));
	}
	let temp_58_0 = (mul_((mul_(a, b)), (mul_(c, b))));
	let temp_58_1 = (mul_((mul_(b, a)), (mul_(c, b))));
	assert(eq_(temp_58_0, temp_58_1)) by {
		cong_mul_(mul_(a, b), mul_(c, b), mul_(b, a), mul_(c, b));
		lemma_mul_comm(a, b);
		lemma_eq_ref(mul_(c, b));
	}
	let temp_59_0 = (mul_((mul_(b, a)), (mod_((mul_(c, b)), m))));
	let temp_59_1 = (mul_((mul_(b, a)), (mod_((add_((mul_((add_((mul_((mod_(c, m)), b)), (mul_(d, (mod_(a, m)))))), m)), (mul_(c, b)))), m))));
	assert(eq_(temp_59_0, temp_59_1)) by {
		lemma_mod_mul_vanish(mul_(c, b), add_(mul_(mod_(c, m), b), mul_(d, mod_(a, m))), m);
		cong_mul_(mul_(b, a), mod_(mul_(c, b), m), mul_(b, a), mod_(add_(mul_(add_(mul_(mod_(c, m), b), mul_(d, mod_(a, m))), m), mul_(c, b)), m));
		lemma_eq_ref(mul_(b, a));
	}
	let temp_60_0 = (mul_((sub_(b, c)), (mul_(a, (mod_(c, m))))));
	let temp_60_1 = (mul_((sub_(b, c)), (mul_(a, (mod_((add_(c, (mul_((mul_((mul_(c, d)), (add_(d, (mod_(a, m)))))), m)))), m))))));
	assert(eq_(temp_60_0, temp_60_1)) by {
		lemma_eq_ref(sub_(b, c));
		lemma_mod_mul_vanish(c, mul_(mul_(c, d), add_(d, mod_(a, m))), m);
		cong_mul_(sub_(b, c), mul_(a, mod_(c, m)), sub_(b, c), mul_(a, mod_(add_(c, mul_(mul_(mul_(c, d), add_(d, mod_(a, m))), m)), m)));
		lemma_eq_ref(a);
		cong_mul_(a, mod_(c, m), a, mod_(add_(c, mul_(mul_(mul_(c, d), add_(d, mod_(a, m))), m)), m));
	}
	let temp_61_0 = (mul_((mul_((mod_(a, m)), c)), (mul_(b, b))));
	let temp_61_1 = (mul_((mul_((mod_(a, m)), c)), (mul_(b, b))));
	assert(eq_(temp_61_0, temp_61_1)) by {
		lemma_eq_ref(temp_61_0);
	}
	let temp_62_0 = (sub_((mul_(a, d)), (add_(c, (mod_(c, m))))));
	let temp_62_1 = (sub_((mul_(d, a)), (add_(c, (mod_(c, m))))));
	assert(eq_(temp_62_0, temp_62_1)) by {
		lemma_mul_comm(a, d);
		cong_sub_(mul_(a, d), add_(c, mod_(c, m)), mul_(d, a), add_(c, mod_(c, m)));
		lemma_eq_ref(add_(c, mod_(c, m)));
	}
	let temp_63_0 = (mul_((mul_(d, a)), (add_(b, d))));
	let temp_63_1 = (mul_(d, (mul_(a, (add_(b, d))))));
	assert(eq_(temp_63_0, temp_63_1)) by {
		lemma_eq_sym(temp_63_1, temp_63_0);
		lemma_mul_assoc(d, a, add_(b, d));
	}
	let temp_64_0 = (mul_((mul_(b, c)), (sub_(d, a))));
	let temp_64_1 = (mul_(b, (mul_(c, (sub_(d, a))))));
	assert(eq_(temp_64_0, temp_64_1)) by {
		lemma_eq_sym(temp_64_1, temp_64_0);
		lemma_mul_assoc(b, c, sub_(d, a));
	}
	let temp_65_0 = (mul_((mod_((mul_(a, b)), m)), (mul_((mod_(b, m)), d))));
	let temp_65_1 = (mul_((mod_((add_((mul_(a, b)), (mul_((add_((mul_(a, d)), (mul_(c, a)))), m)))), m)), (mul_((mod_(b, m)), d))));
	assert(eq_(temp_65_0, temp_65_1)) by {
		lemma_mod_mul_vanish(mul_(a, b), add_(mul_(a, d), mul_(c, a)), m);
		cong_mul_(mod_(mul_(a, b), m), mul_(mod_(b, m), d), mod_(add_(mul_(a, b), mul_(add_(mul_(a, d), mul_(c, a)), m)), m), mul_(mod_(b, m), d));
		lemma_eq_ref(mul_(mod_(b, m), d));
	}
	let temp_66_0 = (mul_((mul_(a, b)), (mul_(d, b))));
	let temp_66_1 = (mul_((mul_(d, b)), (mul_(a, b))));
	assert(eq_(temp_66_0, temp_66_1)) by {
		lemma_mul_comm(mul_(a, b), mul_(d, b));
	}
	let temp_67_0 = (mul_((mul_(a, b)), (mul_(d, b))));
	let temp_67_1 = (mul_(a, (mul_(b, (mul_(d, b))))));
	assert(eq_(temp_67_0, temp_67_1)) by {
		lemma_eq_sym(temp_67_1, temp_67_0);
		lemma_mul_assoc(a, b, mul_(d, b));
	}
	let temp_68_0 = (mul_((sub_(a, a)), (mul_((mod_(b, m)), d))));
	let temp_68_1 = (mul_((sub_(a, a)), (mul_((mod_((add_((mul_((mul_((sub_(c, c)), (mul_(c, a)))), m)), b)), m)), d))));
	assert(eq_(temp_68_0, temp_68_1)) by {
		lemma_mod_mul_vanish(b, mul_(sub_(c, c), mul_(c, a)), m);
		cong_mul_(sub_(a, a), mul_(mod_(b, m), d), sub_(a, a), mul_(mod_(add_(mul_(mul_(sub_(c, c), mul_(c, a)), m), b), m), d));
		lemma_eq_ref(d);
		lemma_eq_ref(sub_(a, a));
		cong_mul_(mod_(b, m), d, mod_(add_(mul_(mul_(sub_(c, c), mul_(c, a)), m), b), m), d);
	}
	let temp_69_0 = (mul_((sub_(d, c)), (mul_(c, a))));
	let temp_69_1 = (mul_((mul_((sub_(d, c)), c)), a));
	assert(eq_(temp_69_0, temp_69_1)) by {
		lemma_mul_assoc(sub_(d, c), c, a);
	}
	let temp_70_0 = (mul_((mul_(a, d)), (mul_(as_elem(89), a))));
	let temp_70_1 = (mul_((mul_(a, d)), (mul_(a, as_elem(89)))));
	assert(eq_(temp_70_0, temp_70_1)) by {
		cong_mul_(mul_(a, d), mul_(as_elem(89), a), mul_(a, d), mul_(a, as_elem(89)));
		lemma_mul_comm(as_elem(89), a);
		lemma_eq_ref(mul_(a, d));
	}
	let temp_71_0 = (mul_((sub_(a, d)), (mul_(b, b))));
	let temp_71_1 = (mul_((mul_((sub_(a, d)), b)), b));
	assert(eq_(temp_71_0, temp_71_1)) by {
		lemma_mul_assoc(sub_(a, d), b, b);
	}
	let temp_72_0 = (mul_((mod_((mul_(a, a)), m)), (add_(a, a))));
	let temp_72_1 = (mul_((mod_((sub_((mul_(a, a)), (mul_((mod_((mul_((mul_(b, (mod_(c, m)))), (sub_(b, c)))), m)), m)))), m)), (add_(a, a))));
	assert(eq_(temp_72_0, temp_72_1)) by {
		lemma_add_comm(a, a);
		lemma_mod_mul_vanish(mul_(a, a), mod_(mul_(mul_(b, mod_(c, m)), sub_(b, c)), m), m);
		cong_mul_(mod_(mul_(a, a), m), add_(a, a), mod_(sub_(mul_(a, a), mul_(mod_(mul_(mul_(b, mod_(c, m)), sub_(b, c)), m), m)), m), add_(a, a));
	}
	let temp_73_0 = (mul_((mul_(a, c)), (sub_(a, c))));
	let temp_73_1 = (mul_(a, (mul_(c, (sub_(a, c))))));
	assert(eq_(temp_73_0, temp_73_1)) by {
		lemma_eq_sym(temp_73_1, temp_73_0);
		lemma_mul_assoc(a, c, sub_(a, c));
	}
	let temp_74_0 = (mul_((mul_((mod_(b, m)), b)), (mul_(b, d))));
	let temp_74_1 = (mul_((mul_((mod_((add_((mul_((mul_((mul_(c, c)), (mul_(d, c)))), m)), b)), m)), b)), (mul_(b, d))));
	assert(eq_(temp_74_0, temp_74_1)) by {
		lemma_mod_mul_vanish(b, mul_(mul_(c, c), mul_(d, c)), m);
		cong_mul_(mul_(mod_(b, m), b), mul_(b, d), mul_(mod_(add_(mul_(mul_(mul_(c, c), mul_(d, c)), m), b), m), b), mul_(b, d));
		lemma_eq_ref(b);
		cong_mul_(mod_(b, m), b, mod_(add_(mul_(mul_(mul_(c, c), mul_(d, c)), m), b), m), b);
		lemma_eq_ref(mul_(b, d));
	}
	let temp_75_0 = (mul_((add_(d, c)), (add_(d, c))));
	let temp_75_1 = (mul_((add_(d, c)), (add_(d, c))));
	assert(eq_(temp_75_0, temp_75_1)) by {
		lemma_eq_ref(temp_75_0);
	}
	let temp_76_0 = (mod_((mul_((mul_(c, a)), (add_(a, c)))), m));
	let temp_76_1 = (mod_((sub_((mul_((mul_(c, a)), (add_(a, c)))), (mul_((mul_((mul_(a, c)), (mul_(c, b)))), m)))), m));
	assert(eq_(temp_76_0, temp_76_1)) by {
		lemma_mod_mul_vanish(mul_(mul_(c, a), add_(a, c)), mul_(mul_(a, c), mul_(c, b)), m);
	}
	let temp_77_0 = (mul_((mul_(d, d)), (mul_(c, d))));
	let temp_77_1 = (mul_((mul_((mul_(d, d)), c)), d));
	assert(eq_(temp_77_0, temp_77_1)) by {
		lemma_mul_assoc(mul_(d, d), c, d);
	}
	let temp_78_0 = (mul_((mul_(as_elem(54), b)), (mul_(a, c))));
	let temp_78_1 = (mul_((mul_((mul_(as_elem(54), b)), a)), c));
	assert(eq_(temp_78_0, temp_78_1)) by {
		lemma_mul_assoc(mul_(as_elem(54), b), a, c);
	}
	let temp_79_0 = (mul_((mul_(b, b)), (mul_(b, b))));
	let temp_79_1 = (mul_((mul_(b, b)), (mul_(b, b))));
	assert(eq_(temp_79_0, temp_79_1)) by {
		lemma_eq_ref(temp_79_0);
	}
	let temp_80_0 = (mul_((mul_(a, b)), (mul_(a, (mod_(c, m))))));
	let temp_80_1 = (mul_(a, (mul_(b, (mul_(a, (mod_(c, m))))))));
	assert(eq_(temp_80_0, temp_80_1)) by {
		lemma_mul_assoc(a, b, mul_(a, mod_(c, m)));
		lemma_eq_sym(temp_80_1, temp_80_0);
	}
	let temp_81_0 = (add_((mod_((mul_(b, c)), m)), (mul_(b, a))));
	let temp_81_1 = (add_((mul_(b, a)), (mod_((mul_(b, c)), m))));
	assert(eq_(temp_81_0, temp_81_1)) by {
		lemma_add_comm(mod_(mul_(b, c), m), mul_(b, a));
	}
	let temp_82_0 = (mod_((mul_((mul_(b, a)), (sub_(b, b)))), m));
	let temp_82_1 = (mod_((mul_(b, (mul_(a, (sub_(b, b)))))), m));
	assert(eq_(temp_82_0, temp_82_1)) by {
		lemma_mul_assoc(b, a, sub_(b, b));
		cong_mod_(mul_(mul_(b, a), sub_(b, b)), m, mul_(b, mul_(a, sub_(b, b))), m);
		lemma_eq_sym(mul_(b, mul_(a, sub_(b, b))), mul_(mul_(b, a), sub_(b, b)));
		lemma_eq_ref(m);
	}
	let temp_83_0 = (mul_((mul_(d, c)), (mul_(d, d))));
	let temp_83_1 = (mul_(d, (mul_(c, (mul_(d, d))))));
	assert(eq_(temp_83_0, temp_83_1)) by {
		lemma_eq_sym(temp_83_1, temp_83_0);
		lemma_mul_assoc(d, c, mul_(d, d));
	}
	let temp_84_0 = (sub_((mul_(c, d)), (mul_(c, d))));
	let temp_84_1 = (sub_((mul_(c, d)), (mul_(d, c))));
	assert(eq_(temp_84_0, temp_84_1)) by {
		cong_sub_(mul_(c, d), mul_(c, d), mul_(c, d), mul_(d, c));
		lemma_mul_comm(c, d);
		lemma_eq_ref(mul_(c, d));
	}
	let temp_85_0 = (mul_((add_(c, (mod_(a, m)))), (mul_(a, d))));
	let temp_85_1 = (add_((mul_(c, (mul_(a, d)))), (mul_((mod_(a, m)), (mul_(a, d))))));
	assert(eq_(temp_85_0, temp_85_1)) by {
		lemma_mul_dist(c, mod_(a, m), mul_(a, d));
	}
	let temp_86_0 = (mul_((sub_(a, d)), (mul_(b, b))));
	let temp_86_1 = (sub_((mul_(a, (mul_(b, b)))), (mul_(d, (mul_(b, b))))));
	assert(eq_(temp_86_0, temp_86_1)) by {
		lemma_mul_dist(mul_(b, b), a, d);
	}
	let temp_87_0 = (sub_((add_(a, a)), (add_(a, a))));
	let temp_87_1 = (sub_((add_(a, a)), (add_(a, a))));
	assert(eq_(temp_87_0, temp_87_1)) by {
		lemma_eq_ref(temp_87_0);
	}
	let temp_88_0 = (mul_((mod_((mul_(c, a)), m)), (add_(c, d))));
	let temp_88_1 = (add_((mul_((mod_((mul_(c, a)), m)), c)), (mul_((mod_((mul_(c, a)), m)), d))));
	assert(eq_(temp_88_0, temp_88_1)) by {
		lemma_mul_dist(mod_(mul_(c, a), m), c, d);
	}
	let temp_89_0 = (mul_((mul_(c, a)), (mul_(b, c))));
	let temp_89_1 = (mul_((mul_(b, c)), (mul_(c, a))));
	assert(eq_(temp_89_0, temp_89_1)) by {
		lemma_mul_comm(mul_(c, a), mul_(b, c));
	}
	let temp_90_0 = (mul_((add_(a, b)), (mul_(d, a))));
	let temp_90_1 = (mul_((mul_((add_(a, b)), d)), a));
	assert(eq_(temp_90_0, temp_90_1)) by {
		lemma_mul_assoc(add_(a, b), d, a);
	}
	let temp_91_0 = (add_((sub_((mod_(a, m)), d)), (mul_(b, c))));
	let temp_91_1 = (add_((sub_((mod_((add_((mul_((mul_((mul_(c, c)), (mul_(a, a)))), m)), a)), m)), d)), (mul_(b, c))));
	assert(eq_(temp_91_0, temp_91_1)) by {
		cong_sub_(mod_(a, m), d, mod_(add_(mul_(mul_(mul_(c, c), mul_(a, a)), m), a), m), d);
		lemma_eq_ref(mul_(b, c));
		lemma_eq_ref(d);
		lemma_mod_mul_vanish(a, mul_(mul_(c, c), mul_(a, a)), m);
		cong_add_(sub_(mod_(a, m), d), mul_(b, c), sub_(mod_(add_(mul_(mul_(mul_(c, c), mul_(a, a)), m), a), m), d), mul_(b, c));
	}
	let temp_92_0 = (add_((mul_(c, (mod_(d, m)))), (sub_((mod_(b, m)), a))));
	let temp_92_1 = (add_((sub_((mod_(b, m)), a)), (mul_(c, (mod_(d, m))))));
	assert(eq_(temp_92_0, temp_92_1)) by {
		lemma_add_comm(mul_(c, mod_(d, m)), sub_(mod_(b, m), a));
	}
	let temp_93_0 = (sub_((mul_(b, b)), (mul_(b, c))));
	let temp_93_1 = (sub_((mul_(b, b)), (mul_(c, b))));
	assert(eq_(temp_93_0, temp_93_1)) by {
		cong_sub_(mul_(b, b), mul_(b, c), mul_(b, b), mul_(c, b));
		lemma_mul_comm(b, b);
		lemma_mul_comm(b, c);
	}
	let temp_94_0 = (mul_((sub_(a, d)), (mul_(c, d))));
	let temp_94_1 = (sub_((mul_(a, (mul_(c, d)))), (mul_(d, (mul_(c, d))))));
	assert(eq_(temp_94_0, temp_94_1)) by {
		lemma_mul_dist(mul_(c, d), a, d);
	}
	let temp_95_0 = (mul_((mul_(b, a)), (mul_(d, a))));
	let temp_95_1 = (mul_((mul_(d, a)), (mul_(b, a))));
	assert(eq_(temp_95_0, temp_95_1)) by {
		lemma_mul_comm(mul_(b, a), mul_(d, a));
	}
	let temp_96_0 = (mod_((sub_((mul_(d, c)), (mul_(b, (mod_(b, m)))))), m));
	let temp_96_1 = (mod_((sub_((mul_(c, d)), (mul_(b, (mod_(b, m)))))), m));
	assert(eq_(temp_96_0, temp_96_1)) by {
		lemma_mul_comm(d, c);
		cong_mod_(sub_(mul_(d, c), mul_(b, mod_(b, m))), m, sub_(mul_(c, d), mul_(b, mod_(b, m))), m);
		lemma_eq_ref(m);
		cong_sub_(mul_(d, c), mul_(b, mod_(b, m)), mul_(c, d), mul_(b, mod_(b, m)));
		lemma_eq_ref(mul_(b, mod_(b, m)));
	}
	let temp_97_0 = (mod_((mul_((add_(b, b)), (add_(b, b)))), m));
	let temp_97_1 = (mod_((sub_((mul_((add_(b, b)), (add_(b, b)))), (mul_((mul_((mul_(c, c)), (mul_(b, c)))), m)))), m));
	assert(eq_(temp_97_0, temp_97_1)) by {
		lemma_mod_mul_vanish(mul_(add_(b, b), add_(b, b)), mul_(mul_(c, c), mul_(b, c)), m);
	}
	let temp_98_0 = (sub_((mul_(d, c)), (mul_((mod_(d, m)), b))));
	let temp_98_1 = (sub_((mul_(c, d)), (mul_((mod_(d, m)), b))));
	assert(eq_(temp_98_0, temp_98_1)) by {
		lemma_mul_comm(d, c);
		cong_sub_(mul_(d, c), mul_(mod_(d, m), b), mul_(c, d), mul_(mod_(d, m), b));
		lemma_eq_ref(mul_(mod_(d, m), b));
	}
	let temp_99_0 = (mul_((mul_(a, a)), (mul_(d, a))));
	let temp_99_1 = (mul_((mul_((mul_(a, a)), d)), a));
	assert(eq_(temp_99_0, temp_99_1)) by {
		lemma_mul_assoc(mul_(a, a), d, a);
	}
	let temp_100_0 = (mul_((mul_(a, b)), (mul_(d, b))));
	let temp_100_1 = (mul_(a, (mul_(b, (mul_(d, b))))));
	assert(eq_(temp_100_0, temp_100_1)) by {
		lemma_eq_sym(temp_100_1, temp_100_0);
		lemma_mul_assoc(a, b, mul_(d, b));
	}
	let temp_101_0 = (mul_((mul_(b, c)), (mul_(d, d))));
	let temp_101_1 = (mul_((mul_((mul_(b, c)), d)), d));
	assert(eq_(temp_101_0, temp_101_1)) by {
		lemma_mul_assoc(mul_(b, c), d, d);
	}
	let temp_102_0 = (mod_((mul_((mul_(c, d)), (mul_(b, b)))), m));
	let temp_102_1 = (mod_((add_((mul_((mul_(a, (mul_(b, d)))), m)), (mul_((mul_(c, d)), (mul_(b, b)))))), m));
	assert(eq_(temp_102_0, temp_102_1)) by {
		lemma_mod_mul_vanish(mul_(mul_(c, d), mul_(b, b)), mul_(a, mul_(b, d)), m);
	}
	let temp_103_0 = (mul_((mul_(d, c)), (mul_(a, b))));
	let temp_103_1 = (mul_((mul_(a, b)), (mul_(d, c))));
	assert(eq_(temp_103_0, temp_103_1)) by {
		lemma_mul_comm(mul_(d, c), mul_(a, b));
	}
	let temp_104_0 = (mul_((add_(c, a)), (mod_((mul_(c, c)), m))));
	let temp_104_1 = (mul_((add_(a, c)), (mod_((mul_(c, c)), m))));
	assert(eq_(temp_104_0, temp_104_1)) by {
		lemma_add_comm(c, a);
		cong_mul_(add_(c, a), mod_(mul_(c, c), m), add_(a, c), mod_(mul_(c, c), m));
		lemma_eq_ref(mod_(mul_(c, c), m));
	}
	let temp_105_0 = (mod_((mul_((mul_(b, a)), (mul_(d, b)))), m));
	let temp_105_1 = (mod_((sub_((mul_((mul_(b, a)), (mul_(d, b)))), (mul_((mul_((mul_(c, c)), (mul_(b, (mod_(c, m)))))), m)))), m));
	assert(eq_(temp_105_0, temp_105_1)) by {
		lemma_mod_mul_vanish(mul_(mul_(b, a), mul_(d, b)), mul_(mul_(c, c), mul_(b, mod_(c, m))), m);
	}
	let temp_106_0 = (mul_((mul_(c, d)), (mul_(d, a))));
	let temp_106_1 = (mul_((mul_((mul_(c, d)), d)), a));
	assert(eq_(temp_106_0, temp_106_1)) by {
		lemma_mul_assoc(mul_(c, d), d, a);
	}
	let temp_107_0 = (mul_((add_(c, a)), (mul_(a, c))));
	let temp_107_1 = (mul_((add_(c, a)), (mul_(c, a))));
	assert(eq_(temp_107_0, temp_107_1)) by {
		cong_mul_(add_(c, a), mul_(a, c), add_(c, a), mul_(c, a));
		lemma_mul_comm(a, c);
		lemma_eq_ref(add_(c, a));
	}
	let temp_108_0 = (mod_((mul_((mul_(c, b)), (mul_(d, as_elem(37))))), m));
	let temp_108_1 = (mod_((mul_((mul_(b, c)), (mul_(d, as_elem(37))))), m));
	assert(eq_(temp_108_0, temp_108_1)) by {
		lemma_mul_comm(c, b);
		cong_mod_(mul_(mul_(c, b), mul_(d, as_elem(37))), m, mul_(mul_(b, c), mul_(d, as_elem(37))), m);
		lemma_eq_ref(mul_(d, as_elem(37)));
		cong_mul_(mul_(c, b), mul_(d, as_elem(37)), mul_(b, c), mul_(d, as_elem(37)));
		lemma_eq_ref(m);
	}
	let temp_109_0 = (mul_((mul_(d, a)), (mul_(d, d))));
	let temp_109_1 = (mul_((mul_(d, a)), (mul_(d, d))));
	assert(eq_(temp_109_0, temp_109_1)) by {
		lemma_eq_ref(temp_109_0);
	}

}

} // verus!