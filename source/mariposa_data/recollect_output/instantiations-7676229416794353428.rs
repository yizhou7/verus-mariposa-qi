use builtin_macros::*;
// use builtin::*;
mod nl_basics;
use crate::nl_basics::*;
verus! {

pub proof fn free_0(a: Elem, b: Elem, c: Elem, d: Elem, m: Elem)
{
	let temp_0_0 = (mul_((mul_(d, b)), b));
	let temp_0_1 = (mul_(d, (mul_(b, b))));
	assert(eq_(temp_0_0, temp_0_1)) by {
		lemma_eq_sym(temp_0_1, temp_0_0);
		lemma_mul_assoc(d, b, b);
	}
	let temp_1_0 = (mul_((mul_(c, c)), (mul_(b, c))));
	let temp_1_1 = (mul_((mul_(c, c)), (mul_(b, c))));
	assert(eq_(temp_1_0, temp_1_1)) by {
		lemma_eq_ref(temp_1_0);
	}
	let temp_2_0 = (mul_((mul_(d, c)), (mul_(b, d))));
	let temp_2_1 = (mul_(d, (mul_(c, (mul_(b, d))))));
	assert(eq_(temp_2_0, temp_2_1)) by {
		lemma_eq_sym(temp_2_1, temp_2_0);
		lemma_mul_assoc(d, c, mul_(b, d));
	}
	let temp_3_0 = (mul_((mul_(c, (mod_(b, m)))), (mul_(d, a))));
	let temp_3_1 = (mul_(c, (mul_((mod_(b, m)), (mul_(d, a))))));
	assert(eq_(temp_3_0, temp_3_1)) by {
		lemma_mul_assoc(c, mod_(b, m), mul_(d, a));
		lemma_eq_sym(temp_3_1, temp_3_0);
	}
	let temp_4_0 = (mod_((mul_((mul_(c, a)), (mod_((mul_(as_elem(31), a)), m)))), m));
	let temp_4_1 = (mod_((mod_((mul_((mul_(c, a)), (mul_(as_elem(31), a)))), m)), m));
	assert(eq_(temp_4_0, temp_4_1)) by {
		lemma_mod_mul_noop(mul_(c, a), mul_(as_elem(31), a), m);
		lemma_eq_sym(temp_4_1, temp_4_0);
	}
	let temp_5_0 = (sub_((sub_((mod_(d, m)), d)), (mul_(d, a))));
	let temp_5_1 = (sub_((sub_((mod_(d, m)), d)), (mul_(a, d))));
	assert(eq_(temp_5_0, temp_5_1)) by {
		cong_sub_(sub_(mod_(d, m), d), mul_(d, a), sub_(mod_(d, m), d), mul_(a, d));
		lemma_mul_comm(d, a);
		lemma_eq_ref(sub_(mod_(d, m), d));
	}
	let temp_6_0 = (sub_((mul_(a, b)), (mul_(d, d))));
	let temp_6_1 = (sub_((mul_(a, b)), (mul_(d, d))));
	assert(eq_(temp_6_0, temp_6_1)) by {
		lemma_eq_ref(temp_6_0);
	}
	let temp_7_0 = (mod_((mul_((mul_(d, a)), (add_(c, a)))), m));
	let temp_7_1 = (mod_((add_((mul_((mul_(d, a)), c)), (mul_((mul_(d, a)), a)))), m));
	assert(eq_(temp_7_0, temp_7_1)) by {
		lemma_mul_dist(mul_(d, a), c, a);
		cong_mod_(mul_(mul_(d, a), add_(c, a)), m, add_(mul_(mul_(d, a), c), mul_(mul_(d, a), a)), m);
		lemma_eq_ref(m);
	}
	let temp_8_0 = (mul_((mul_(b, b)), (mul_(c, d))));
	let temp_8_1 = (mul_((mul_(b, b)), (mul_(c, d))));
	assert(eq_(temp_8_0, temp_8_1)) by {
		lemma_eq_ref(temp_8_0);
	}
	let temp_9_0 = (sub_((mod_((mul_(b, a)), m)), (mul_(a, (mod_(b, m))))));
	let temp_9_1 = (sub_((mod_((mul_(a, b)), m)), (mul_(a, (mod_(b, m))))));
	assert(eq_(temp_9_0, temp_9_1)) by {
		lemma_mul_comm(b, a);
		cong_sub_(mod_(mul_(b, a), m), mul_(a, mod_(b, m)), mod_(mul_(a, b), m), mul_(a, mod_(b, m)));
		lemma_eq_ref(m);
		cong_mod_(mul_(b, a), m, mul_(a, b), m);
		lemma_eq_ref(mul_(a, mod_(b, m)));
	}
	let temp_10_0 = (mul_((add_(d, a)), (mul_(b, b))));
	let temp_10_1 = (mul_((add_(d, a)), (mul_(b, b))));
	assert(eq_(temp_10_0, temp_10_1)) by {
		lemma_eq_ref(temp_10_0);
	}
	let temp_11_0 = (sub_((mod_((add_(b, d)), m)), (mul_(c, d))));
	let temp_11_1 = (sub_((mod_((add_(d, b)), m)), (mul_(c, d))));
	assert(eq_(temp_11_0, temp_11_1)) by {
		lemma_add_comm(b, d);
		cong_sub_(mod_(add_(b, d), m), mul_(c, d), mod_(add_(d, b), m), mul_(c, d));
		cong_mod_(add_(b, d), m, add_(d, b), m);
		lemma_eq_ref(mul_(c, d));
		lemma_eq_ref(m);
	}
	let temp_12_0 = (mod_((mul_((mul_(a, c)), (mul_(as_elem(69), b)))), m));
	let temp_12_1 = (mod_((add_((mul_((mul_(a, c)), (mul_(as_elem(69), b)))), (mul_((mod_((mul_((mul_(b, d)), (mul_(d, a)))), m)), m)))), m));
	assert(eq_(temp_12_0, temp_12_1)) by {
		lemma_mod_mul_vanish(mul_(mul_(a, c), mul_(as_elem(69), b)), mod_(mul_(mul_(b, d), mul_(d, a)), m), m);
	}
	let temp_13_0 = (sub_((mul_(c, d)), (mul_(b, c))));
	let temp_13_1 = (sub_((mul_(c, d)), (mul_(c, b))));
	assert(eq_(temp_13_0, temp_13_1)) by {
		cong_sub_(mul_(c, d), mul_(b, c), mul_(c, d), mul_(c, b));
		lemma_mul_comm(b, c);
		lemma_eq_ref(mul_(c, d));
	}
	let temp_14_0 = (mod_((add_((add_(c, c)), (mul_(a, b)))), m));
	let temp_14_1 = (mod_((add_((mod_((add_(c, c)), m)), (mul_(a, b)))), m));
	assert(eq_(temp_14_0, temp_14_1)) by {
		lemma_mod_add_noop(add_(c, c), mul_(a, b), m);
	}
	let temp_15_0 = (add_((mod_((add_(b, a)), m)), (mul_(d, a))));
	let temp_15_1 = (add_((mod_((add_((mod_(b, m)), (mod_(a, m)))), m)), (mul_(d, a))));
	assert(eq_(temp_15_0, temp_15_1)) by {
		lemma_mod_add_noop(b, a, m);
		cong_add_(mod_(add_(b, a), m), mul_(d, a), mod_(add_(mod_(b, m), mod_(a, m)), m), mul_(d, a));
		lemma_eq_ref(mul_(d, a));
	}
	let temp_16_0 = (mul_((mul_(b, a)), (mul_(b, b))));
	let temp_16_1 = (mul_((mul_((mul_(b, a)), b)), b));
	assert(eq_(temp_16_0, temp_16_1)) by {
		lemma_mul_assoc(mul_(b, a), b, b);
	}
	let temp_17_0 = (mul_((mul_((mod_(a, m)), a)), (mul_(a, d))));
	let temp_17_1 = (mul_((mul_((mod_(a, m)), a)), (mul_(d, a))));
	assert(eq_(temp_17_0, temp_17_1)) by {
		cong_mul_(mul_(mod_(a, m), a), mul_(a, d), mul_(mod_(a, m), a), mul_(d, a));
		lemma_mul_comm(a, d);
		lemma_eq_ref(mul_(mod_(a, m), a));
	}
	let temp_18_0 = (mod_((mul_((mul_(as_elem(45), d)), (add_(a, c)))), m));
	let temp_18_1 = (mod_((add_((mul_((mul_(as_elem(45), d)), a)), (mul_((mul_(as_elem(45), d)), c)))), m));
	assert(eq_(temp_18_0, temp_18_1)) by {
		lemma_mul_dist(mul_(as_elem(45), d), a, c);
		cong_mod_(mul_(mul_(as_elem(45), d), add_(a, c)), m, add_(mul_(mul_(as_elem(45), d), a), mul_(mul_(as_elem(45), d), c)), m);
		lemma_eq_ref(m);
	}
	let temp_19_0 = (mod_((mul_((mul_(c, b)), (mul_(d, d)))), m));
	let temp_19_1 = (mod_((mul_((mul_(b, c)), (mul_(d, d)))), m));
	assert(eq_(temp_19_0, temp_19_1)) by {
		lemma_mul_comm(c, b);
		lemma_mul_comm(d, d);
		cong_mod_(mul_(mul_(c, b), mul_(d, d)), m, mul_(mul_(b, c), mul_(d, d)), m);
		cong_mul_(mul_(c, b), mul_(d, d), mul_(b, c), mul_(d, d));
		lemma_eq_ref(m);
	}
	let temp_20_0 = (mul_(b, (mul_(b, b))));
	let temp_20_1 = (mul_(b, (mul_(b, b))));
	assert(eq_(temp_20_0, temp_20_1)) by {
		lemma_eq_ref(temp_20_0);
	}
	let temp_21_0 = (mod_((mul_((add_(as_elem(50), (mod_(c, m)))), (sub_(a, a)))), m));
	let temp_21_1 = (mod_((add_((mul_(as_elem(50), (sub_(a, a)))), (mul_((mod_(c, m)), (sub_(a, a)))))), m));
	assert(eq_(temp_21_0, temp_21_1)) by {
		lemma_mul_dist(as_elem(50), mod_(c, m), sub_(a, a));
		cong_mod_(mul_(add_(as_elem(50), mod_(c, m)), sub_(a, a)), m, add_(mul_(as_elem(50), sub_(a, a)), mul_(mod_(c, m), sub_(a, a))), m);
		lemma_eq_ref(m);
	}
	let temp_22_0 = (mod_((mul_((add_(a, c)), c)), m));
	let temp_22_1 = (mod_((mul_((add_(c, a)), c)), m));
	assert(eq_(temp_22_0, temp_22_1)) by {
		lemma_add_comm(a, c);
		cong_mod_(mul_(add_(a, c), c), m, mul_(add_(c, a), c), m);
		lemma_eq_ref(c);
		lemma_eq_ref(m);
		cong_mul_(add_(a, c), c, add_(c, a), c);
	}
	let temp_23_0 = (sub_((mul_(d, a)), (mul_(d, c))));
	let temp_23_1 = (sub_((mul_(d, a)), (mul_(c, d))));
	assert(eq_(temp_23_0, temp_23_1)) by {
		cong_sub_(mul_(d, a), mul_(d, c), mul_(d, a), mul_(c, d));
		lemma_mul_comm(d, c);
		lemma_eq_ref(mul_(d, a));
	}
	let temp_24_0 = (mod_((sub_((mul_(c, b)), (mul_(b, d)))), m));
	let temp_24_1 = (mod_((add_((sub_((mul_(c, b)), (mul_(b, d)))), (mul_((add_(b, (mul_(a, c)))), m)))), m));
	assert(eq_(temp_24_0, temp_24_1)) by {
		lemma_mod_mul_vanish(sub_(mul_(c, b), mul_(b, d)), add_(b, mul_(a, c)), m);
	}
	let temp_25_0 = (mod_((mul_((mul_(d, b)), (mul_(d, (mod_(c, m)))))), m));
	let temp_25_1 = (mod_((mul_(d, (mul_(b, (mul_(d, (mod_(c, m)))))))), m));
	assert(eq_(temp_25_0, temp_25_1)) by {
		lemma_mul_assoc(d, b, mul_(d, mod_(c, m)));
		cong_mod_(mul_(mul_(d, b), mul_(d, mod_(c, m))), m, mul_(d, mul_(b, mul_(d, mod_(c, m)))), m);
		lemma_eq_ref(m);
		lemma_eq_sym(mul_(d, mul_(b, mul_(d, mod_(c, m)))), mul_(mul_(d, b), mul_(d, mod_(c, m))));
	}
	let temp_26_0 = (mod_((mul_((mul_(a, as_elem(32))), (mul_(a, d)))), m));
	let temp_26_1 = (mod_((mul_((mul_(as_elem(32), a)), (mul_(a, d)))), m));
	assert(eq_(temp_26_0, temp_26_1)) by {
		lemma_mul_comm(a, as_elem(32));
		cong_mod_(mul_(mul_(a, as_elem(32)), mul_(a, d)), m, mul_(mul_(as_elem(32), a), mul_(a, d)), m);
		lemma_eq_ref(mul_(a, d));
		cong_mul_(mul_(a, as_elem(32)), mul_(a, d), mul_(as_elem(32), a), mul_(a, d));
		lemma_eq_ref(m);
	}
	let temp_27_0 = (mul_((mul_(a, c)), (mul_(a, (mod_(d, m))))));
	let temp_27_1 = (mul_((mul_((mul_(a, c)), a)), (mod_(d, m))));
	assert(eq_(temp_27_0, temp_27_1)) by {
		lemma_mul_assoc(mul_(a, c), a, mod_(d, m));
	}
	let temp_28_0 = (mul_((mul_(b, c)), (mul_(c, d))));
	let temp_28_1 = (mul_((mul_((mul_(b, c)), c)), d));
	assert(eq_(temp_28_0, temp_28_1)) by {
		lemma_mul_assoc(mul_(b, c), c, d);
	}
	let temp_29_0 = (mul_((sub_(a, a)), (mul_(a, d))));
	let temp_29_1 = (sub_((mul_(a, (mul_(a, d)))), (mul_(a, (mul_(a, d))))));
	assert(eq_(temp_29_0, temp_29_1)) by {
		lemma_mul_dist(mul_(a, d), a, a);
	}
	let temp_30_0 = (mul_((sub_(b, d)), (add_(b, (mod_(c, m))))));
	let temp_30_1 = (add_((mul_((sub_(b, d)), b)), (mul_((sub_(b, d)), (mod_(c, m))))));
	assert(eq_(temp_30_0, temp_30_1)) by {
		lemma_mul_dist(sub_(b, d), b, mod_(c, m));
	}
	let temp_31_0 = (mul_((sub_(c, b)), (mul_(b, a))));
	let temp_31_1 = (sub_((mul_(c, (mul_(b, a)))), (mul_(b, (mul_(b, a))))));
	assert(eq_(temp_31_0, temp_31_1)) by {
		lemma_mul_dist(mul_(b, a), c, b);
	}
	let temp_32_0 = (mul_((mul_(a, b)), (mod_((sub_(d, c)), m))));
	let temp_32_1 = (mul_((mul_(a, b)), (mod_((add_((mul_((mul_((mul_((mod_(d, m)), a)), (mul_(a, a)))), m)), (sub_(d, c)))), m))));
	assert(eq_(temp_32_0, temp_32_1)) by {
		lemma_mod_mul_vanish(sub_(d, c), mul_(mul_(mod_(d, m), a), mul_(a, a)), m);
		cong_mul_(mul_(a, b), mod_(sub_(d, c), m), mul_(a, b), mod_(add_(mul_(mul_(mul_(mod_(d, m), a), mul_(a, a)), m), sub_(d, c)), m));
		lemma_eq_ref(mul_(a, b));
	}
	let temp_33_0 = (mul_((mul_(c, d)), (sub_(a, c))));
	let temp_33_1 = (mul_(c, (mul_(d, (sub_(a, c))))));
	assert(eq_(temp_33_0, temp_33_1)) by {
		lemma_eq_sym(temp_33_1, temp_33_0);
		lemma_mul_assoc(c, d, sub_(a, c));
	}
	let temp_34_0 = (sub_((add_(a, b)), (mul_(a, (mod_(c, m))))));
	let temp_34_1 = (sub_((add_(a, b)), (mul_((mod_(c, m)), a))));
	assert(eq_(temp_34_0, temp_34_1)) by {
		lemma_mul_comm(a, mod_(c, m));
		cong_sub_(add_(a, b), mul_(a, mod_(c, m)), add_(a, b), mul_(mod_(c, m), a));
		lemma_eq_ref(add_(a, b));
	}
	let temp_35_0 = (mul_((mul_(c, d)), (mul_(a, a))));
	let temp_35_1 = (mul_(c, (mul_(d, (mul_(a, a))))));
	assert(eq_(temp_35_0, temp_35_1)) by {
		lemma_eq_sym(temp_35_1, temp_35_0);
		lemma_mul_assoc(c, d, mul_(a, a));
	}
	let temp_36_0 = (mul_((mul_(b, c)), (mul_(b, c))));
	let temp_36_1 = (mul_((mul_(b, c)), (mul_(c, b))));
	assert(eq_(temp_36_0, temp_36_1)) by {
		cong_mul_(mul_(b, c), mul_(b, c), mul_(b, c), mul_(c, b));
		lemma_mul_comm(b, c);
		lemma_eq_ref(mul_(b, c));
	}
	let temp_37_0 = (add_((mod_((sub_(c, d)), m)), (mul_(b, a))));
	let temp_37_1 = (add_((mul_(b, a)), (mod_((sub_(c, d)), m))));
	assert(eq_(temp_37_0, temp_37_1)) by {
		lemma_add_comm(mod_(sub_(c, d), m), mul_(b, a));
	}
	let temp_38_0 = (sub_((sub_(c, c)), (mul_(b, a))));
	let temp_38_1 = (sub_((sub_(c, c)), (mul_(a, b))));
	assert(eq_(temp_38_0, temp_38_1)) by {
		cong_sub_(sub_(c, c), mul_(b, a), sub_(c, c), mul_(a, b));
		lemma_mul_comm(b, a);
		lemma_eq_ref(sub_(c, c));
	}
	let temp_39_0 = (mul_((add_((mod_(d, m)), (mod_(a, m)))), (mod_((mul_(b, (mod_(c, m)))), m))));
	let temp_39_1 = (mul_((add_((mod_(d, m)), (mod_(a, m)))), (mod_((mul_((mod_(c, m)), b)), m))));
	assert(eq_(temp_39_0, temp_39_1)) by {
		lemma_mul_comm(mod_(c, m), b);
		cong_mul_(add_(mod_(d, m), mod_(a, m)), mod_(mul_(b, mod_(c, m)), m), add_(mod_(d, m), mod_(a, m)), mod_(mul_(mod_(c, m), b), m));
		cong_mod_(mul_(mod_(c, m), b), m, mul_(b, mod_(c, m)), m);
		lemma_eq_ref(m);
		lemma_eq_ref(add_(mod_(d, m), mod_(a, m)));
		lemma_eq_sym(mod_(mul_(mod_(c, m), b), m), mod_(mul_(b, mod_(c, m)), m));
	}
	let temp_40_0 = (mul_((mul_(a, a)), (mod_((mul_(c, (mod_(as_elem(20), m)))), m))));
	let temp_40_1 = (mul_((mul_(a, a)), (mod_((mod_((mul_(c, as_elem(20))), m)), m))));
	assert(eq_(temp_40_0, temp_40_1)) by {
		lemma_mul_comm(a, a);
		lemma_mod_mul_noop(c, as_elem(20), m);
		cong_mul_(mul_(a, a), mod_(mul_(c, mod_(as_elem(20), m)), m), mul_(a, a), mod_(mod_(mul_(c, as_elem(20)), m), m));
		lemma_eq_sym(mod_(mod_(mul_(c, as_elem(20)), m), m), mod_(mul_(c, mod_(as_elem(20), m)), m));
	}
	let temp_41_0 = (mul_((mul_(b, c)), (mod_((mul_(a, b)), m))));
	let temp_41_1 = (mul_((mul_(b, c)), (mod_((add_((mul_((mul_((mul_((mod_(d, m)), c)), (mul_(d, c)))), m)), (mul_(a, b)))), m))));
	assert(eq_(temp_41_0, temp_41_1)) by {
		lemma_mod_mul_vanish(mul_(a, b), mul_(mul_(mod_(d, m), c), mul_(d, c)), m);
		cong_mul_(mul_(b, c), mod_(mul_(a, b), m), mul_(b, c), mod_(add_(mul_(mul_(mul_(mod_(d, m), c), mul_(d, c)), m), mul_(a, b)), m));
		lemma_eq_ref(mul_(b, c));
	}
	let temp_42_0 = (mul_((sub_(b, d)), (mul_((mod_(b, m)), c))));
	let temp_42_1 = (sub_((mul_(b, (mul_((mod_(b, m)), c)))), (mul_(d, (mul_((mod_(b, m)), c))))));
	assert(eq_(temp_42_0, temp_42_1)) by {
		lemma_mul_dist(mul_(mod_(b, m), c), b, d);
	}
	let temp_43_0 = (mul_((mul_(c, (mod_(d, m)))), (sub_((mod_(a, m)), d))));
	let temp_43_1 = (mul_((mul_(c, (mod_(d, m)))), (sub_((mod_((sub_(a, (mul_((add_((mul_(a, d)), (mul_(d, b)))), m)))), m)), d))));
	assert(eq_(temp_43_0, temp_43_1)) by {
		lemma_mod_mul_vanish(a, add_(mul_(a, d), mul_(d, b)), m);
		cong_mul_(mul_(c, mod_(d, m)), sub_(mod_(a, m), d), mul_(c, mod_(d, m)), sub_(mod_(sub_(a, mul_(add_(mul_(a, d), mul_(d, b)), m)), m), d));
		cong_sub_(mod_(a, m), d, mod_(sub_(a, mul_(add_(mul_(a, d), mul_(d, b)), m)), m), d);
		lemma_eq_ref(mul_(c, mod_(d, m)));
		lemma_eq_ref(d);
	}
	let temp_44_0 = (mul_((mul_(a, (mod_(c, m)))), (mod_((mul_(a, b)), m))));
	let temp_44_1 = (mul_(a, (mul_((mod_(c, m)), (mod_((mul_(a, b)), m))))));
	assert(eq_(temp_44_0, temp_44_1)) by {
		lemma_mul_assoc(a, mod_(c, m), mod_(mul_(a, b), m));
		lemma_eq_sym(temp_44_1, temp_44_0);
	}
	let temp_45_0 = (mul_((add_(b, (mod_(c, m)))), (mul_(d, c))));
	let temp_45_1 = (mul_((mul_(d, c)), (add_(b, (mod_(c, m))))));
	assert(eq_(temp_45_0, temp_45_1)) by {
		lemma_mul_comm(add_(b, mod_(c, m)), mul_(d, c));
	}
	let temp_46_0 = (mul_((mul_(c, a)), (mul_(c, as_elem(32)))));
	let temp_46_1 = (mul_((mul_((mul_(c, a)), c)), as_elem(32)));
	assert(eq_(temp_46_0, temp_46_1)) by {
		lemma_mul_assoc(mul_(c, a), c, as_elem(32));
	}
	let temp_47_0 = (sub_((mul_(d, b)), (sub_((mod_(a, m)), c))));
	let temp_47_1 = (sub_((mul_(d, b)), (sub_((mod_((add_((mul_((mul_((mul_(a, b)), (mul_(d, (mod_(c, m)))))), m)), a)), m)), c))));
	assert(eq_(temp_47_0, temp_47_1)) by {
		lemma_mod_mul_vanish(a, mul_(mul_(a, b), mul_(d, mod_(c, m))), m);
		cong_sub_(mul_(d, b), sub_(mod_(a, m), c), mul_(d, b), sub_(mod_(add_(mul_(mul_(mul_(a, b), mul_(d, mod_(c, m))), m), a), m), c));
		cong_sub_(mod_(a, m), c, mod_(add_(mul_(mul_(mul_(a, b), mul_(d, mod_(c, m))), m), a), m), c);
		lemma_eq_ref(mul_(d, b));
		lemma_eq_ref(c);
	}
	let temp_48_0 = (mul_((mul_(a, c)), (mul_(c, d))));
	let temp_48_1 = (mul_((mul_(c, d)), (mul_(a, c))));
	assert(eq_(temp_48_0, temp_48_1)) by {
		lemma_mul_comm(mul_(a, c), mul_(c, d));
	}
	let temp_49_0 = (add_((mod_((sub_(b, b)), m)), (mul_(c, as_elem(98)))));
	let temp_49_1 = (add_((mod_((sub_((mod_(b, m)), (mod_(b, m)))), m)), (mul_(c, as_elem(98)))));
	assert(eq_(temp_49_0, temp_49_1)) by {
		cong_add_(mod_(sub_(b, b), m), mul_(c, as_elem(98)), mod_(sub_(mod_(b, m), mod_(b, m)), m), mul_(c, as_elem(98)));
		lemma_mod_sub_noop(b, b, m);
		lemma_eq_ref(mul_(c, as_elem(98)));
	}
	let temp_50_0 = (mul_((mul_((mod_(a, m)), a)), (mod_((mul_(c, c)), m))));
	let temp_50_1 = (mul_((mod_((mul_(c, c)), m)), (mul_((mod_(a, m)), a))));
	assert(eq_(temp_50_0, temp_50_1)) by {
		lemma_mul_comm(mul_(mod_(a, m), a), mod_(mul_(c, c), m));
	}
	let temp_51_0 = (mul_((mul_(a, b)), (mul_(c, (mod_(d, m))))));
	let temp_51_1 = (mul_((mul_((mul_(a, b)), c)), (mod_(d, m))));
	assert(eq_(temp_51_0, temp_51_1)) by {
		lemma_mul_assoc(mul_(a, b), c, mod_(d, m));
	}
	let temp_52_0 = (mul_((mul_(c, c)), (mod_((mul_((mod_(a, m)), b)), m))));
	let temp_52_1 = (mul_(c, (mul_(c, (mod_((mul_((mod_(a, m)), b)), m))))));
	assert(eq_(temp_52_0, temp_52_1)) by {
		lemma_mul_assoc(c, c, mod_(mul_(mod_(a, m), b), m));
		lemma_eq_sym(temp_52_1, temp_52_0);
	}
	let temp_53_0 = (mul_((mul_(d, c)), (mul_(a, d))));
	let temp_53_1 = (mul_(d, (mul_(c, (mul_(a, d))))));
	assert(eq_(temp_53_0, temp_53_1)) by {
		lemma_eq_sym(temp_53_1, temp_53_0);
		lemma_mul_assoc(d, c, mul_(a, d));
	}
	let temp_54_0 = (mul_((mul_(d, b)), (mul_(b, a))));
	let temp_54_1 = (mul_((mul_(d, b)), (mul_(a, b))));
	assert(eq_(temp_54_0, temp_54_1)) by {
		cong_mul_(mul_(d, b), mul_(b, a), mul_(d, b), mul_(a, b));
		lemma_mul_comm(b, a);
		lemma_eq_ref(mul_(d, b));
	}
	let temp_55_0 = (mul_((mul_(b, b)), (mul_(a, a))));
	let temp_55_1 = (mul_((mul_((mul_(b, b)), a)), a));
	assert(eq_(temp_55_0, temp_55_1)) by {
		lemma_mul_assoc(mul_(b, b), a, a);
	}
	let temp_56_0 = (mul_((sub_(c, (mod_(d, m)))), (mod_((mul_(d, c)), m))));
	let temp_56_1 = (sub_((mul_(c, (mod_((mul_(d, c)), m)))), (mul_((mod_(d, m)), (mod_((mul_(d, c)), m))))));
	assert(eq_(temp_56_0, temp_56_1)) by {
		lemma_mul_dist(mod_(mul_(d, c), m), c, mod_(d, m));
	}
	let temp_57_0 = (mul_((mul_((mod_(c, m)), b)), (mul_(a, as_elem(46)))));
	let temp_57_1 = (mul_((mul_((mod_(c, m)), b)), (mul_(as_elem(46), a))));
	assert(eq_(temp_57_0, temp_57_1)) by {
		lemma_mul_comm(a, as_elem(46));
		cong_mul_(mul_(mod_(c, m), b), mul_(a, as_elem(46)), mul_(mod_(c, m), b), mul_(as_elem(46), a));
		lemma_eq_ref(mul_(mod_(c, m), b));
	}
	let temp_58_0 = (mul_((mul_(d, c)), a));
	let temp_58_1 = (mul_(d, (mul_(c, a))));
	assert(eq_(temp_58_0, temp_58_1)) by {
		lemma_eq_sym(temp_58_1, temp_58_0);
		lemma_mul_assoc(d, c, a);
	}
	let temp_59_0 = (sub_((mul_(as_elem(100), a)), (mul_(c, d))));
	let temp_59_1 = (sub_((mul_(a, as_elem(100))), (mul_(c, d))));
	assert(eq_(temp_59_0, temp_59_1)) by {
		lemma_mul_comm(as_elem(100), a);
		cong_sub_(mul_(as_elem(100), a), mul_(c, d), mul_(a, as_elem(100)), mul_(c, d));
		lemma_eq_ref(mul_(c, d));
	}
	let temp_60_0 = (sub_((mul_(c, b)), (mul_(d, c))));
	let temp_60_1 = (sub_((mul_(b, c)), (mul_(d, c))));
	assert(eq_(temp_60_0, temp_60_1)) by {
		cong_sub_(mul_(c, b), mul_(d, c), mul_(b, c), mul_(d, c));
		lemma_mul_comm(c, b);
		lemma_eq_ref(mul_(d, c));
	}
	let temp_61_0 = (mul_((mul_(c, c)), (mod_((mul_(c, d)), m))));
	let temp_61_1 = (mul_((mul_(c, c)), (mod_((sub_((mul_(c, d)), (mul_((mul_((mul_(a, a)), (mul_(b, d)))), m)))), m))));
	assert(eq_(temp_61_0, temp_61_1)) by {
		lemma_mul_comm(c, c);
		lemma_mod_mul_vanish(mul_(c, d), mul_(mul_(a, a), mul_(b, d)), m);
		cong_mul_(mul_(c, c), mod_(mul_(c, d), m), mul_(c, c), mod_(sub_(mul_(c, d), mul_(mul_(mul_(a, a), mul_(b, d)), m)), m));
	}
	let temp_62_0 = (mul_((mul_((mod_(b, m)), d)), (sub_(c, c))));
	let temp_62_1 = (mul_((mul_((mod_((add_((mul_((mul_((mul_(d, b)), (mul_(a, a)))), m)), b)), m)), d)), (sub_(c, c))));
	assert(eq_(temp_62_0, temp_62_1)) by {
		lemma_mod_mul_vanish(b, mul_(mul_(d, b), mul_(a, a)), m);
		cong_mul_(mul_(mod_(b, m), d), sub_(c, c), mul_(mod_(add_(mul_(mul_(mul_(d, b), mul_(a, a)), m), b), m), d), sub_(c, c));
		lemma_eq_ref(d);
		cong_mul_(mod_(b, m), d, mod_(add_(mul_(mul_(mul_(d, b), mul_(a, a)), m), b), m), d);
		lemma_eq_ref(sub_(c, c));
	}
	let temp_63_0 = (add_((mul_(c, b)), (mul_(c, a))));
	let temp_63_1 = (add_((mul_(c, a)), (mul_(c, b))));
	assert(eq_(temp_63_0, temp_63_1)) by {
		lemma_add_comm(mul_(c, b), mul_(c, a));
	}
	let temp_64_0 = (mul_((mul_(d, a)), (add_(a, a))));
	let temp_64_1 = (mul_((mul_(a, d)), (add_(a, a))));
	assert(eq_(temp_64_0, temp_64_1)) by {
		cong_mul_(mul_(d, a), add_(a, a), mul_(a, d), add_(a, a));
		lemma_add_comm(a, a);
		lemma_mul_comm(d, a);
	}
	let temp_65_0 = (mul_((mul_(a, c)), (mul_(c, b))));
	let temp_65_1 = (mul_(a, (mul_(c, (mul_(c, b))))));
	assert(eq_(temp_65_0, temp_65_1)) by {
		lemma_eq_sym(temp_65_1, temp_65_0);
		lemma_mul_assoc(a, c, mul_(c, b));
	}
	let temp_66_0 = (mul_((mod_((mul_(as_elem(98), (mod_(b, m)))), m)), (mul_(a, d))));
	let temp_66_1 = (mul_((mod_((sub_((mul_(as_elem(98), (mod_(b, m)))), (mul_((mul_((sub_(c, b)), (mul_(c, b)))), m)))), m)), (mul_(a, d))));
	assert(eq_(temp_66_0, temp_66_1)) by {
		cong_mul_(mod_(mul_(as_elem(98), mod_(b, m)), m), mul_(a, d), mod_(sub_(mul_(as_elem(98), mod_(b, m)), mul_(mul_(sub_(c, b), mul_(c, b)), m)), m), mul_(a, d));
		lemma_mod_mul_vanish(mul_(as_elem(98), mod_(b, m)), mul_(sub_(c, b), mul_(c, b)), m);
		lemma_eq_ref(mul_(a, d));
	}
	let temp_67_0 = (mul_((mul_(d, a)), (sub_(b, a))));
	let temp_67_1 = (mul_(d, (mul_(a, (sub_(b, a))))));
	assert(eq_(temp_67_0, temp_67_1)) by {
		lemma_eq_sym(temp_67_1, temp_67_0);
		lemma_mul_assoc(d, a, sub_(b, a));
	}
	let temp_68_0 = (mod_((mul_((mul_(c, c)), (mul_(a, b)))), m));
	let temp_68_1 = (mod_((mul_((mul_(c, c)), (mul_(a, b)))), m));
	assert(eq_(temp_68_0, temp_68_1)) by {
		lemma_eq_ref(temp_68_0);
	}
	let temp_69_0 = (add_((mul_(a, b)), (mod_((add_(c, c)), m))));
	let temp_69_1 = (add_((mul_(a, b)), (mod_((add_((mul_((sub_((sub_(a, a)), (mul_(b, d)))), m)), (add_(c, c)))), m))));
	assert(eq_(temp_69_0, temp_69_1)) by {
		lemma_mod_mul_vanish(add_(c, c), sub_(sub_(a, a), mul_(b, d)), m);
		cong_add_(mul_(a, b), mod_(add_(c, c), m), mul_(a, b), mod_(add_(mul_(sub_(sub_(a, a), mul_(b, d)), m), add_(c, c)), m));
		lemma_eq_ref(mul_(a, b));
	}
	let temp_70_0 = (mul_((mul_(c, (mod_(b, m)))), (mul_(b, d))));
	let temp_70_1 = (mul_((mul_(c, (mod_(b, m)))), (mul_(d, b))));
	assert(eq_(temp_70_0, temp_70_1)) by {
		lemma_mul_comm(b, d);
		cong_mul_(mul_(c, mod_(b, m)), mul_(b, d), mul_(c, mod_(b, m)), mul_(d, b));
		lemma_eq_ref(mul_(c, mod_(b, m)));
	}
	let temp_71_0 = (mul_((mul_(a, d)), (mul_(c, a))));
	let temp_71_1 = (mul_((mul_(a, d)), (mul_(a, c))));
	assert(eq_(temp_71_0, temp_71_1)) by {
		cong_mul_(mul_(a, d), mul_(c, a), mul_(a, d), mul_(a, c));
		lemma_mul_comm(c, a);
		lemma_eq_ref(mul_(a, d));
	}
	let temp_72_0 = (mul_((mul_((mod_(a, m)), (mod_(d, m)))), (mul_(c, (mod_(b, m))))));
	let temp_72_1 = (mul_((mul_((mod_(d, m)), (mod_(a, m)))), (mul_(c, (mod_(b, m))))));
	assert(eq_(temp_72_0, temp_72_1)) by {
		lemma_mul_comm(mod_(a, m), mod_(d, m));
		cong_mul_(mul_(mod_(a, m), mod_(d, m)), mul_(c, mod_(b, m)), mul_(mod_(d, m), mod_(a, m)), mul_(c, mod_(b, m)));
		lemma_eq_ref(mul_(c, mod_(b, m)));
	}
	let temp_73_0 = (mul_((mul_((mod_(a, m)), a)), (mul_(b, c))));
	let temp_73_1 = (mul_((mul_((mul_((mod_(a, m)), a)), b)), c));
	assert(eq_(temp_73_0, temp_73_1)) by {
		lemma_mul_assoc(mul_(mod_(a, m), a), b, c);
	}
	let temp_74_0 = (sub_((sub_(a, a)), (mul_(a, b))));
	let temp_74_1 = (sub_((sub_(a, a)), (mul_(b, a))));
	assert(eq_(temp_74_0, temp_74_1)) by {
		cong_sub_(sub_(a, a), mul_(a, b), sub_(a, a), mul_(b, a));
		lemma_mul_comm(a, b);
		cong_sub_(a, a, a, a);
		lemma_eq_ref(a);
	}
	let temp_75_0 = (mul_((add_(d, (mod_(a, m)))), (sub_(d, (mod_(d, m))))));
	let temp_75_1 = (mul_((add_((mod_(a, m)), d)), (sub_(d, (mod_(d, m))))));
	assert(eq_(temp_75_0, temp_75_1)) by {
		lemma_add_comm(d, mod_(a, m));
		cong_mul_(add_(d, mod_(a, m)), sub_(d, mod_(d, m)), add_(mod_(a, m), d), sub_(d, mod_(d, m)));
		lemma_eq_ref(sub_(d, mod_(d, m)));
	}
	let temp_76_0 = (mul_((mul_(b, (mod_(a, m)))), (sub_(d, a))));
	let temp_76_1 = (mul_((mul_(b, (mod_((add_((mul_((mul_((mul_(b, b)), (add_(c, b)))), m)), a)), m)))), (sub_(d, a))));
	assert(eq_(temp_76_0, temp_76_1)) by {
		lemma_mod_mul_vanish(a, mul_(mul_(b, b), add_(c, b)), m);
		cong_mul_(mul_(b, mod_(a, m)), sub_(d, a), mul_(b, mod_(add_(mul_(mul_(mul_(b, b), add_(c, b)), m), a), m)), sub_(d, a));
		lemma_eq_ref(b);
		cong_mul_(b, mod_(a, m), b, mod_(add_(mul_(mul_(mul_(b, b), add_(c, b)), m), a), m));
		lemma_eq_ref(sub_(d, a));
	}
	let temp_77_0 = (mul_((mul_(a, b)), (mul_(a, c))));
	let temp_77_1 = (mul_((mul_(b, a)), (mul_(a, c))));
	assert(eq_(temp_77_0, temp_77_1)) by {
		cong_mul_(mul_(a, b), mul_(a, c), mul_(b, a), mul_(a, c));
		lemma_mul_comm(a, b);
		lemma_eq_ref(mul_(a, c));
	}
	let temp_78_0 = (mod_((mul_((mul_(b, c)), (add_(c, d)))), m));
	let temp_78_1 = (mod_((add_((mul_((mul_((mul_(b, b)), (add_(d, d)))), m)), (mul_((mul_(b, c)), (add_(c, d)))))), m));
	assert(eq_(temp_78_0, temp_78_1)) by {
		lemma_mod_mul_vanish(mul_(mul_(b, c), add_(c, d)), mul_(mul_(b, b), add_(d, d)), m);
	}
	let temp_79_0 = (mul_((add_(c, a)), (mod_((mul_(as_elem(85), a)), m))));
	let temp_79_1 = (mul_((add_(a, c)), (mod_((mul_(as_elem(85), a)), m))));
	assert(eq_(temp_79_0, temp_79_1)) by {
		lemma_add_comm(c, a);
		cong_mul_(add_(c, a), mod_(mul_(as_elem(85), a), m), add_(a, c), mod_(mul_(as_elem(85), a), m));
		lemma_eq_ref(mod_(mul_(as_elem(85), a), m));
	}
	let temp_80_0 = (mod_((mul_((mul_(a, c)), (mul_(c, a)))), m));
	let temp_80_1 = (mod_((add_((mul_((mod_((add_((mod_((mul_(d, d)), m)), (mul_((mod_(c, m)), b)))), m)), m)), (mul_((mul_(a, c)), (mul_(c, a)))))), m));
	assert(eq_(temp_80_0, temp_80_1)) by {
		lemma_mod_mul_vanish(mul_(mul_(a, c), mul_(c, a)), mod_(add_(mod_(mul_(d, d), m), mul_(mod_(c, m), b)), m), m);
	}
	let temp_81_0 = (mul_((mul_(c, b)), (mod_((mul_(b, a)), m))));
	let temp_81_1 = (mul_((mul_(b, c)), (mod_((mul_(b, a)), m))));
	assert(eq_(temp_81_0, temp_81_1)) by {
		lemma_mul_comm(c, b);
		cong_mul_(mul_(c, b), mod_(mul_(b, a), m), mul_(b, c), mod_(mul_(b, a), m));
		lemma_eq_ref(mod_(mul_(b, a), m));
	}
	let temp_82_0 = (mod_((mul_((mul_(as_elem(73), b)), (mul_(c, b)))), m));
	let temp_82_1 = (mod_((mul_(as_elem(73), (mul_(b, (mul_(c, b)))))), m));
	assert(eq_(temp_82_0, temp_82_1)) by {
		lemma_mul_assoc(as_elem(73), b, mul_(c, b));
		cong_mod_(mul_(mul_(as_elem(73), b), mul_(c, b)), m, mul_(as_elem(73), mul_(b, mul_(c, b))), m);
		lemma_eq_sym(mul_(as_elem(73), mul_(b, mul_(c, b))), mul_(mul_(as_elem(73), b), mul_(c, b)));
		lemma_eq_ref(m);
	}
	let temp_83_0 = (sub_((mod_((mul_(b, a)), m)), (mod_((add_(d, b)), m))));
	let temp_83_1 = (sub_((mod_((mul_(b, a)), m)), (mod_((add_(b, d)), m))));
	assert(eq_(temp_83_0, temp_83_1)) by {
		lemma_add_comm(d, b);
		cong_sub_(mod_(mul_(b, a), m), mod_(add_(d, b), m), mod_(mul_(b, a), m), mod_(add_(b, d), m));
		lemma_eq_ref(mod_(mul_(b, a), m));
		cong_mod_(add_(d, b), m, add_(b, d), m);
		lemma_eq_ref(m);
	}
	let temp_84_0 = (mul_((add_(d, c)), (mul_(c, d))));
	let temp_84_1 = (mul_((mul_(c, d)), (add_(d, c))));
	assert(eq_(temp_84_0, temp_84_1)) by {
		lemma_mul_comm(add_(d, c), mul_(c, d));
	}
	let temp_85_0 = (mul_((mul_(d, (mod_(d, m)))), (mul_((mod_(a, m)), b))));
	let temp_85_1 = (mul_((mul_((mul_(d, (mod_(d, m)))), (mod_(a, m)))), b));
	assert(eq_(temp_85_0, temp_85_1)) by {
		lemma_mul_assoc(mul_(d, mod_(d, m)), mod_(a, m), b);
	}
	let temp_86_0 = (mul_((mul_(c, (mod_(b, m)))), (mul_(a, (mod_(a, m))))));
	let temp_86_1 = (mul_((mul_(a, (mod_(a, m)))), (mul_(c, (mod_(b, m))))));
	assert(eq_(temp_86_0, temp_86_1)) by {
		lemma_mul_comm(mul_(c, mod_(b, m)), mul_(a, mod_(a, m)));
	}
	let temp_87_0 = (add_((mul_(d, (mod_(b, m)))), (mul_(c, a))));
	let temp_87_1 = (add_((mul_(c, a)), (mul_(d, (mod_(b, m))))));
	assert(eq_(temp_87_0, temp_87_1)) by {
		lemma_add_comm(mul_(d, mod_(b, m)), mul_(c, a));
	}
	let temp_88_0 = (sub_((mul_(a, c)), (mod_((mul_(b, a)), m))));
	let temp_88_1 = (sub_((mul_(c, a)), (mod_((mul_(b, a)), m))));
	assert(eq_(temp_88_0, temp_88_1)) by {
		lemma_mul_comm(a, c);
		cong_sub_(mul_(a, c), mod_(mul_(b, a), m), mul_(c, a), mod_(mul_(b, a), m));
		lemma_eq_ref(mod_(mul_(b, a), m));
	}
	let temp_89_0 = (mul_((sub_(d, b)), (mod_((mul_(c, (mod_(c, m)))), m))));
	let temp_89_1 = (mul_((sub_(d, b)), (mod_((mod_((mul_(c, c)), m)), m))));
	assert(eq_(temp_89_0, temp_89_1)) by {
		lemma_mod_mul_noop(c, c, m);
		cong_mul_(sub_(d, b), mod_(mul_(c, mod_(c, m)), m), sub_(d, b), mod_(mod_(mul_(c, c), m), m));
		lemma_eq_sym(mod_(mod_(mul_(c, c), m), m), mod_(mul_(c, mod_(c, m)), m));
		lemma_eq_ref(sub_(d, b));
	}
	let temp_90_0 = (add_((mul_(c, a)), (mul_(a, b))));
	let temp_90_1 = (add_((mul_(c, a)), (mul_(b, a))));
	assert(eq_(temp_90_0, temp_90_1)) by {
		cong_add_(mul_(c, a), mul_(a, b), mul_(c, a), mul_(b, a));
		lemma_mul_comm(a, b);
		lemma_eq_ref(mul_(c, a));
	}
	let temp_91_0 = (mul_((mul_((mod_(b, m)), b)), (mul_(b, b))));
	let temp_91_1 = (mul_((mul_(b, b)), (mul_((mod_(b, m)), b))));
	assert(eq_(temp_91_0, temp_91_1)) by {
		lemma_mul_comm(mul_(mod_(b, m), b), mul_(b, b));
	}
	let temp_92_0 = (mul_((mul_(d, b)), a));
	let temp_92_1 = (mul_(d, (mul_(b, a))));
	assert(eq_(temp_92_0, temp_92_1)) by {
		lemma_eq_sym(temp_92_1, temp_92_0);
		lemma_mul_assoc(d, b, a);
	}
	let temp_93_0 = (mul_((mul_(d, b)), (mul_(b, d))));
	let temp_93_1 = (mul_((mul_(d, b)), (mul_(d, b))));
	assert(eq_(temp_93_0, temp_93_1)) by {
		cong_mul_(mul_(d, b), mul_(b, d), mul_(d, b), mul_(d, b));
		lemma_mul_comm(b, d);
		lemma_eq_ref(mul_(d, b));
	}
	let temp_94_0 = (sub_((mul_(b, d)), (add_(c, a))));
	let temp_94_1 = (sub_((mul_(d, b)), (add_(c, a))));
	assert(eq_(temp_94_0, temp_94_1)) by {
		cong_sub_(mul_(b, d), add_(c, a), mul_(d, b), add_(c, a));
		lemma_mul_comm(b, d);
		lemma_eq_ref(add_(c, a));
	}
	let temp_95_0 = (mul_((mul_(c, d)), (sub_(c, b))));
	let temp_95_1 = (mul_(c, (mul_(d, (sub_(c, b))))));
	assert(eq_(temp_95_0, temp_95_1)) by {
		lemma_eq_sym(temp_95_1, temp_95_0);
		lemma_mul_assoc(c, d, sub_(c, b));
	}
	let temp_96_0 = (mul_((mul_(b, (mod_(a, m)))), (sub_((mod_(a, m)), a))));
	let temp_96_1 = (mul_(b, (mul_((mod_(a, m)), (sub_((mod_(a, m)), a))))));
	assert(eq_(temp_96_0, temp_96_1)) by {
		lemma_eq_sym(temp_96_1, temp_96_0);
		lemma_mul_assoc(b, mod_(a, m), sub_(mod_(a, m), a));
	}
	let temp_97_0 = (mul_((mul_(d, c)), (mul_(a, d))));
	let temp_97_1 = (mul_((mul_(c, d)), (mul_(a, d))));
	assert(eq_(temp_97_0, temp_97_1)) by {
		cong_mul_(mul_(d, c), mul_(a, d), mul_(c, d), mul_(a, d));
		lemma_mul_comm(d, c);
		lemma_eq_ref(mul_(a, d));
	}
	let temp_98_0 = (add_((mod_((mul_(c, b)), m)), (mod_((mul_(b, b)), m))));
	let temp_98_1 = (add_((mod_((mul_(b, c)), m)), (mod_((mul_(b, b)), m))));
	assert(eq_(temp_98_0, temp_98_1)) by {
		lemma_mul_comm(c, b);
		cong_add_(mod_(mul_(c, b), m), mod_(mul_(b, b), m), mod_(mul_(b, c), m), mod_(mul_(b, b), m));
		lemma_eq_ref(m);
		lemma_eq_ref(mod_(mul_(b, b), m));
		cong_mod_(mul_(c, b), m, mul_(b, c), m);
	}
	let temp_99_0 = (mul_((mul_(b, b)), b));
	let temp_99_1 = (mul_(b, (mul_(b, b))));
	assert(eq_(temp_99_0, temp_99_1)) by {
		lemma_mul_comm(mul_(b, b), b);
	}
	let temp_100_0 = (mul_((mul_(as_elem(78), d)), (mul_(d, d))));
	let temp_100_1 = (mul_((mul_(d, d)), (mul_(as_elem(78), d))));
	assert(eq_(temp_100_0, temp_100_1)) by {
		lemma_mul_comm(mul_(as_elem(78), d), mul_(d, d));
	}
	let temp_101_0 = (mod_((mul_((sub_(c, (mod_(a, m)))), (mul_(a, a)))), m));
	let temp_101_1 = (mod_((mul_((mul_((sub_(c, (mod_(a, m)))), a)), a)), m));
	assert(eq_(temp_101_0, temp_101_1)) by {
		lemma_mul_assoc(sub_(c, mod_(a, m)), a, a);
		cong_mod_(mul_(sub_(c, mod_(a, m)), mul_(a, a)), m, mul_(mul_(sub_(c, mod_(a, m)), a), a), m);
		lemma_eq_ref(m);
	}
	let temp_102_0 = (mul_((mul_(a, b)), (sub_((mod_(a, m)), a))));
	let temp_102_1 = (mul_((sub_((mod_(a, m)), a)), (mul_(a, b))));
	assert(eq_(temp_102_0, temp_102_1)) by {
		lemma_mul_comm(mul_(a, b), sub_(mod_(a, m), a));
	}
	let temp_103_0 = (mod_((mul_((mod_((sub_(c, c)), m)), (mul_(a, d)))), m));
	let temp_103_1 = (mod_((sub_((mul_((mod_((sub_(c, c)), m)), (mul_(a, d)))), (mul_((mul_((mul_(c, d)), (mul_(a, d)))), m)))), m));
	assert(eq_(temp_103_0, temp_103_1)) by {
		lemma_mod_mul_vanish(mul_(mod_(sub_(c, c), m), mul_(a, d)), mul_(mul_(c, d), mul_(a, d)), m);
	}
	let temp_104_0 = (mul_((mul_(d, a)), (mul_((mod_(b, m)), a))));
	let temp_104_1 = (mul_((mul_(d, a)), (mul_((mod_((add_(b, (mul_((mul_((mul_((mod_(c, m)), b)), (mul_(a, c)))), m)))), m)), a))));
	assert(eq_(temp_104_0, temp_104_1)) by {
		lemma_mod_mul_vanish(b, mul_(mul_(mod_(c, m), b), mul_(a, c)), m);
		cong_mul_(mul_(d, a), mul_(mod_(b, m), a), mul_(d, a), mul_(mod_(add_(b, mul_(mul_(mul_(mod_(c, m), b), mul_(a, c)), m)), m), a));
		lemma_eq_ref(a);
		cong_mul_(mod_(b, m), a, mod_(add_(b, mul_(mul_(mul_(mod_(c, m), b), mul_(a, c)), m)), m), a);
		lemma_eq_ref(mul_(d, a));
	}
	let temp_105_0 = (mul_((mod_((mul_(c, c)), m)), (mul_(b, c))));
	let temp_105_1 = (mul_((mul_((mod_((mul_(c, c)), m)), b)), c));
	assert(eq_(temp_105_0, temp_105_1)) by {
		lemma_mul_assoc(mod_(mul_(c, c), m), b, c);
	}
	let temp_106_0 = (sub_((mul_(b, b)), (sub_(b, a))));
	let temp_106_1 = (sub_((mul_(b, b)), (sub_(b, a))));
	assert(eq_(temp_106_0, temp_106_1)) by {
		lemma_eq_ref(temp_106_0);
	}
	let temp_107_0 = (mul_((mul_(a, a)), (add_(a, d))));
	let temp_107_1 = (mul_((mul_(a, a)), (add_(d, a))));
	assert(eq_(temp_107_0, temp_107_1)) by {
		cong_mul_(mul_(a, a), add_(a, d), mul_(a, a), add_(d, a));
		lemma_add_comm(a, d);
		lemma_mul_comm(a, a);
	}
	let temp_108_0 = (sub_((mul_(b, d)), (mul_(a, b))));
	let temp_108_1 = (sub_((mul_(b, d)), (mul_(b, a))));
	assert(eq_(temp_108_0, temp_108_1)) by {
		cong_sub_(mul_(b, d), mul_(a, b), mul_(b, d), mul_(b, a));
		lemma_mul_comm(a, b);
		lemma_eq_ref(mul_(b, d));
	}
	let temp_109_0 = (add_((sub_(a, c)), (mul_(c, c))));
	let temp_109_1 = (add_((sub_(a, c)), (mul_(c, c))));
	assert(eq_(temp_109_0, temp_109_1)) by {
		lemma_eq_ref(temp_109_0);
	}
	let temp_110_0 = (mul_((mul_(d, c)), (mul_(a, (mod_(c, m))))));
	let temp_110_1 = (mul_(d, (mul_(c, (mul_(a, (mod_(c, m))))))));
	assert(eq_(temp_110_0, temp_110_1)) by {
		lemma_mul_assoc(d, c, mul_(a, mod_(c, m)));
		lemma_eq_sym(temp_110_1, temp_110_0);
	}
	let temp_111_0 = (sub_((mod_((mul_(b, b)), m)), (mul_(d, b))));
	let temp_111_1 = (sub_((mod_((mul_(b, b)), m)), (mul_(d, b))));
	assert(eq_(temp_111_0, temp_111_1)) by {
		lemma_eq_ref(temp_111_0);
	}
	let temp_112_0 = (mul_((mul_((mod_(c, m)), d)), (mul_(a, c))));
	let temp_112_1 = (mul_((mul_((mod_((add_(c, (mul_((mod_((add_((mul_((mod_(c, m)), d)), c)), m)), m)))), m)), d)), (mul_(a, c))));
	assert(eq_(temp_112_0, temp_112_1)) by {
		lemma_mod_mul_vanish(c, mod_(add_(mul_(mod_(c, m), d), c), m), m);
		cong_mul_(mul_(mod_(c, m), d), mul_(a, c), mul_(mod_(add_(c, mul_(mod_(add_(mul_(mod_(c, m), d), c), m), m)), m), d), mul_(a, c));
		lemma_eq_ref(d);
		cong_mul_(mod_(c, m), d, mod_(add_(c, mul_(mod_(add_(mul_(mod_(c, m), d), c), m), m)), m), d);
		lemma_eq_ref(mul_(a, c));
	}
	let temp_113_0 = (mul_((mul_(d, a)), (mul_(a, b))));
	let temp_113_1 = (mul_((mul_((mul_(d, a)), a)), b));
	assert(eq_(temp_113_0, temp_113_1)) by {
		lemma_mul_assoc(mul_(d, a), a, b);
	}
	let temp_114_0 = (mul_((mod_((mul_(c, a)), m)), (mul_(d, c))));
	let temp_114_1 = (mul_((mul_((mod_((mul_(c, a)), m)), d)), c));
	assert(eq_(temp_114_0, temp_114_1)) by {
		lemma_mul_assoc(mod_(mul_(c, a), m), d, c);
	}
	let temp_115_0 = (mul_((mul_(a, a)), (mul_(d, c))));
	let temp_115_1 = (mul_((mul_(a, a)), (mul_(d, c))));
	assert(eq_(temp_115_0, temp_115_1)) by {
		lemma_eq_ref(temp_115_0);
	}
	let temp_116_0 = (mul_((sub_(a, d)), (mul_(b, d))));
	let temp_116_1 = (mul_((mul_(b, d)), (sub_(a, d))));
	assert(eq_(temp_116_0, temp_116_1)) by {
		lemma_mul_comm(sub_(a, d), mul_(b, d));
	}
	let temp_117_0 = (mul_((mul_(c, a)), (mul_(a, a))));
	let temp_117_1 = (mul_((mul_(c, a)), (mul_(a, a))));
	assert(eq_(temp_117_0, temp_117_1)) by {
		lemma_eq_ref(temp_117_0);
	}
	let temp_118_0 = (mod_((mul_((add_(d, b)), (mul_(b, c)))), m));
	let temp_118_1 = (mod_((mul_((add_(b, d)), (mul_(b, c)))), m));
	assert(eq_(temp_118_0, temp_118_1)) by {
		lemma_add_comm(d, b);
		cong_mod_(mul_(add_(d, b), mul_(b, c)), m, mul_(add_(b, d), mul_(b, c)), m);
		cong_mul_(add_(d, b), mul_(b, c), add_(b, d), mul_(b, c));
		lemma_eq_ref(m);
		lemma_eq_ref(mul_(b, c));
	}
	let temp_119_0 = (mul_((mod_((mul_(c, b)), m)), (mod_((add_(b, b)), m))));
	let temp_119_1 = (mul_((mod_((mul_(c, b)), m)), (mod_((add_(b, b)), m))));
	assert(eq_(temp_119_0, temp_119_1)) by {
		lemma_eq_ref(temp_119_0);
	}
	let temp_120_0 = (mod_((add_((mul_(a, c)), (mul_(a, d)))), m));
	let temp_120_1 = (mod_((add_((mod_((mul_(a, c)), m)), (mul_(a, d)))), m));
	assert(eq_(temp_120_0, temp_120_1)) by {
		lemma_mod_add_noop(mul_(a, c), mul_(a, d), m);
	}
	let temp_121_0 = (mul_((add_(b, a)), (mul_(d, b))));
	let temp_121_1 = (mul_((add_(a, b)), (mul_(d, b))));
	assert(eq_(temp_121_0, temp_121_1)) by {
		cong_mul_(add_(b, a), mul_(d, b), add_(a, b), mul_(d, b));
		lemma_add_comm(b, a);
		lemma_eq_ref(mul_(d, b));
	}
	let temp_122_0 = (mul_((mod_((mul_(d, (mod_(c, m)))), m)), (mul_((mod_(b, m)), d))));
	let temp_122_1 = (mul_((mod_((sub_((mul_(d, (mod_(c, m)))), (mul_((mul_((add_(a, d)), (mul_(a, c)))), m)))), m)), (mul_((mod_(b, m)), d))));
	assert(eq_(temp_122_0, temp_122_1)) by {
		lemma_mod_mul_vanish(mul_(d, mod_(c, m)), mul_(add_(a, d), mul_(a, c)), m);
		cong_mul_(mod_(mul_(d, mod_(c, m)), m), mul_(mod_(b, m), d), mod_(sub_(mul_(d, mod_(c, m)), mul_(mul_(add_(a, d), mul_(a, c)), m)), m), mul_(mod_(b, m), d));
		lemma_eq_ref(mul_(mod_(b, m), d));
	}
	let temp_123_0 = (mod_((mul_((mul_(a, a)), (sub_(b, b)))), m));
	let temp_123_1 = (mod_((mul_(a, (mul_(a, (sub_(b, b)))))), m));
	assert(eq_(temp_123_0, temp_123_1)) by {
		lemma_mul_assoc(a, a, sub_(b, b));
		cong_mod_(mul_(mul_(a, a), sub_(b, b)), m, mul_(a, mul_(a, sub_(b, b))), m);
		lemma_eq_sym(mul_(a, mul_(a, sub_(b, b))), mul_(mul_(a, a), sub_(b, b)));
		lemma_eq_ref(m);
	}
	let temp_124_0 = (mul_((mul_((mod_(a, m)), a)), (mod_((mul_(d, d)), m))));
	let temp_124_1 = (mul_((mod_(a, m)), (mul_(a, (mod_((mul_(d, d)), m))))));
	assert(eq_(temp_124_0, temp_124_1)) by {
		lemma_mul_assoc(mod_(a, m), a, mod_(mul_(d, d), m));
		lemma_eq_sym(temp_124_1, temp_124_0);
	}
	let temp_125_0 = (mul_((mul_((mod_(a, m)), c)), (mod_((mul_(d, a)), m))));
	let temp_125_1 = (mul_((mul_((mod_((sub_(a, (mul_((mul_((mul_(b, b)), (mod_((add_(a, (mod_(a, m)))), m)))), m)))), m)), c)), (mod_((mul_(d, a)), m))));
	assert(eq_(temp_125_0, temp_125_1)) by {
		cong_mul_(mod_(a, m), c, mod_(sub_(a, mul_(mul_(mul_(b, b), mod_(add_(a, mod_(a, m)), m)), m)), m), c);
		lemma_eq_ref(mod_(mul_(d, a), m));
		lemma_eq_ref(c);
		cong_mul_(mul_(mod_(a, m), c), mod_(mul_(d, a), m), mul_(mod_(sub_(a, mul_(mul_(mul_(b, b), mod_(add_(a, mod_(a, m)), m)), m)), m), c), mod_(mul_(d, a), m));
		lemma_mod_mul_vanish(a, mul_(mul_(b, b), mod_(add_(a, mod_(a, m)), m)), m);
	}
	let temp_126_0 = (add_((mul_(d, b)), (mul_(a, b))));
	let temp_126_1 = (mul_((add_(d, a)), b));
	assert(eq_(temp_126_0, temp_126_1)) by {
		lemma_eq_sym(temp_126_1, temp_126_0);
		lemma_mul_dist(d, a, b);
	}
	let temp_127_0 = (mul_((mul_(d, c)), (sub_(a, b))));
	let temp_127_1 = (mul_((sub_(a, b)), (mul_(d, c))));
	assert(eq_(temp_127_0, temp_127_1)) by {
		lemma_mul_comm(mul_(d, c), sub_(a, b));
	}
	let temp_128_0 = (mul_((mod_((sub_((mod_(a, m)), a)), m)), (mul_(b, a))));
	let temp_128_1 = (mul_((mod_((sub_((mod_((sub_(a, (mul_((mul_((mul_(a, a)), (mul_(c, a)))), m)))), m)), a)), m)), (mul_(b, a))));
	assert(eq_(temp_128_0, temp_128_1)) by {
		lemma_mod_mul_vanish(a, mul_(mul_(a, a), mul_(c, a)), m);
		cong_mul_(mod_(sub_(mod_(a, m), a), m), mul_(b, a), mod_(sub_(mod_(sub_(a, mul_(mul_(mul_(a, a), mul_(c, a)), m)), m), a), m), mul_(b, a));
		cong_mod_(sub_(mod_(a, m), a), m, sub_(mod_(sub_(a, mul_(mul_(mul_(a, a), mul_(c, a)), m)), m), a), m);
		lemma_eq_ref(mul_(b, a));
		lemma_eq_ref(a);
		cong_sub_(mod_(a, m), a, mod_(sub_(a, mul_(mul_(mul_(a, a), mul_(c, a)), m)), m), a);
		lemma_eq_ref(m);
	}
	let temp_129_0 = (mul_((mul_(a, b)), (mul_((mod_(b, m)), c))));
	let temp_129_1 = (mul_((mul_(b, a)), (mul_((mod_(b, m)), c))));
	assert(eq_(temp_129_0, temp_129_1)) by {
		lemma_mul_comm(a, b);
		cong_mul_(mul_(a, b), mul_(mod_(b, m), c), mul_(b, a), mul_(mod_(b, m), c));
		lemma_eq_ref(mul_(mod_(b, m), c));
	}
	let temp_130_0 = (mul_((mul_(a, b)), (mul_(d, (mod_(b, m))))));
	let temp_130_1 = (mul_((mul_(a, b)), (mul_(d, (mod_((sub_(b, (mul_((mul_((mul_(as_elem(38), a)), (mul_(c, c)))), m)))), m))))));
	assert(eq_(temp_130_0, temp_130_1)) by {
		cong_mul_(mul_(a, b), mul_(d, mod_(b, m)), mul_(a, b), mul_(d, mod_(sub_(b, mul_(mul_(mul_(as_elem(38), a), mul_(c, c)), m)), m)));
		lemma_mod_mul_vanish(b, mul_(mul_(as_elem(38), a), mul_(c, c)), m);
		cong_mul_(d, mod_(b, m), d, mod_(sub_(b, mul_(mul_(mul_(as_elem(38), a), mul_(c, c)), m)), m));
		lemma_eq_ref(d);
		lemma_eq_ref(mul_(a, b));
	}
	let temp_131_0 = (mul_((sub_(d, c)), (mul_(d, a))));
	let temp_131_1 = (mul_((mul_(d, a)), (sub_(d, c))));
	assert(eq_(temp_131_0, temp_131_1)) by {
		lemma_mul_comm(sub_(d, c), mul_(d, a));
	}
	let temp_132_0 = (add_((mul_(c, b)), (mul_(b, a))));
	let temp_132_1 = (add_((mul_(c, b)), (mul_(a, b))));
	assert(eq_(temp_132_0, temp_132_1)) by {
		cong_add_(mul_(c, b), mul_(b, a), mul_(c, b), mul_(a, b));
		lemma_mul_comm(b, a);
		lemma_eq_ref(mul_(c, b));
	}
	let temp_133_0 = (mul_((mul_(a, (mod_(a, m)))), (mul_(a, d))));
	let temp_133_1 = (mul_(a, (mul_((mod_(a, m)), (mul_(a, d))))));
	assert(eq_(temp_133_0, temp_133_1)) by {
		lemma_eq_sym(temp_133_1, temp_133_0);
		lemma_mul_assoc(a, mod_(a, m), mul_(a, d));
	}
	let temp_134_0 = (sub_((mul_(d, d)), (mul_(a, a))));
	let temp_134_1 = (sub_((mul_(d, d)), (mul_(a, a))));
	assert(eq_(temp_134_0, temp_134_1)) by {
		lemma_eq_ref(temp_134_0);
	}
	let temp_135_0 = (mul_((mul_(c, b)), (mul_(c, c))));
	let temp_135_1 = (mul_((mul_(b, c)), (mul_(c, c))));
	assert(eq_(temp_135_0, temp_135_1)) by {
		cong_mul_(mul_(c, b), mul_(c, c), mul_(b, c), mul_(c, c));
		lemma_mul_comm(c, b);
		lemma_mul_comm(c, c);
	}
	let temp_136_0 = (mul_((sub_(a, b)), (mul_(a, a))));
	let temp_136_1 = (sub_((mul_(a, (mul_(a, a)))), (mul_(b, (mul_(a, a))))));
	assert(eq_(temp_136_0, temp_136_1)) by {
		lemma_mul_dist(mul_(a, a), a, b);
	}

}

} // verus!