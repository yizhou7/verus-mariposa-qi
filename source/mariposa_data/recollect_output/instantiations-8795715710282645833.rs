use builtin_macros::*;
// use builtin::*;
mod nl_basics;
use crate::nl_basics::*;
verus! {

pub proof fn free_0(a: Elem, b: Elem, c: Elem, d: Elem, m: Elem)
{
	let temp_0_0 = (mul_((mul_(a, a)), (add_(c, c))));
	let temp_0_1 = (mul_((mul_(a, a)), (add_(c, c))));
	assert(eq_(temp_0_0, temp_0_1)) by {
		lemma_eq_ref(temp_0_0);
	}
	let temp_1_0 = (mul_((mul_(d, b)), (mul_(b, a))));
	let temp_1_1 = (mul_((mul_(d, b)), (mul_(a, b))));
	assert(eq_(temp_1_0, temp_1_1)) by {
		cong_mul_(mul_(d, b), mul_(b, a), mul_(d, b), mul_(a, b));
		lemma_mul_comm(b, a);
		lemma_eq_ref(mul_(d, b));
	}
	let temp_2_0 = (mod_((mul_((mul_(d, (mod_(c, m)))), (mul_(a, b)))), m));
	let temp_2_1 = (mod_((mul_((mul_(d, (mod_(c, m)))), (mul_(b, a)))), m));
	assert(eq_(temp_2_0, temp_2_1)) by {
		lemma_mul_comm(a, b);
		cong_mod_(mul_(mul_(d, mod_(c, m)), mul_(a, b)), m, mul_(mul_(d, mod_(c, m)), mul_(b, a)), m);
		lemma_eq_ref(m);
		lemma_eq_ref(mul_(d, mod_(c, m)));
		cong_mul_(mul_(d, mod_(c, m)), mul_(a, b), mul_(d, mod_(c, m)), mul_(b, a));
	}
	let temp_3_0 = (mul_((mul_(a, d)), (mod_((mul_(a, c)), m))));
	let temp_3_1 = (mul_(a, (mul_(d, (mod_((mul_(a, c)), m))))));
	assert(eq_(temp_3_0, temp_3_1)) by {
		lemma_mul_assoc(a, d, mod_(mul_(a, c), m));
		lemma_eq_sym(temp_3_1, temp_3_0);
	}
	let temp_4_0 = (mul_((mod_((sub_(a, b)), m)), (mod_((sub_(c, a)), m))));
	let temp_4_1 = (mul_((mod_((sub_(c, a)), m)), (mod_((sub_(a, b)), m))));
	assert(eq_(temp_4_0, temp_4_1)) by {
		lemma_mul_comm(mod_(sub_(a, b), m), mod_(sub_(c, a), m));
	}
	let temp_5_0 = (mul_((mul_(c, b)), (mul_(as_elem(34), b))));
	let temp_5_1 = (mul_((mul_(c, b)), (mul_(b, as_elem(34)))));
	assert(eq_(temp_5_0, temp_5_1)) by {
		cong_mul_(mul_(c, b), mul_(as_elem(34), b), mul_(c, b), mul_(b, as_elem(34)));
		lemma_mul_comm(as_elem(34), b);
		lemma_eq_ref(mul_(c, b));
	}
	let temp_6_0 = (mul_((mod_((mul_(as_elem(57), b)), m)), (mul_((mod_(d, m)), (mod_(b, m))))));
	let temp_6_1 = (mul_((mod_((mul_(as_elem(57), b)), m)), (mul_((mod_((sub_(d, (mul_((mul_((mul_(d, a)), (mul_(d, c)))), m)))), m)), (mod_(b, m))))));
	assert(eq_(temp_6_0, temp_6_1)) by {
		cong_mul_(mod_(mul_(as_elem(57), b), m), mul_(mod_(d, m), mod_(b, m)), mod_(mul_(as_elem(57), b), m), mul_(mod_(sub_(d, mul_(mul_(mul_(d, a), mul_(d, c)), m)), m), mod_(b, m)));
		lemma_mod_mul_vanish(d, mul_(mul_(d, a), mul_(d, c)), m);
		lemma_eq_ref(mod_(mul_(as_elem(57), b), m));
		cong_mul_(mod_(d, m), mod_(b, m), mod_(sub_(d, mul_(mul_(mul_(d, a), mul_(d, c)), m)), m), mod_(b, m));
		lemma_eq_ref(mod_(b, m));
	}
	let temp_7_0 = (add_((mul_(b, a)), (mul_(as_elem(83), b))));
	let temp_7_1 = (add_((mul_(as_elem(83), b)), (mul_(b, a))));
	assert(eq_(temp_7_0, temp_7_1)) by {
		lemma_add_comm(mul_(b, a), mul_(as_elem(83), b));
	}
	let temp_8_0 = (mul_((mul_(c, a)), c));
	let temp_8_1 = (mul_(c, (mul_(a, c))));
	assert(eq_(temp_8_0, temp_8_1)) by {
		lemma_eq_sym(temp_8_1, temp_8_0);
		lemma_mul_assoc(c, a, c);
	}
	let temp_9_0 = (add_((mod_((mul_(d, (mod_(d, m)))), m)), (add_(a, c))));
	let temp_9_1 = (add_((mod_((mul_(d, (mod_(d, m)))), m)), (add_(c, a))));
	assert(eq_(temp_9_0, temp_9_1)) by {
		lemma_add_comm(a, c);
		cong_add_(mod_(mul_(d, mod_(d, m)), m), add_(a, c), mod_(mul_(d, mod_(d, m)), m), add_(c, a));
		lemma_eq_ref(mod_(mul_(d, mod_(d, m)), m));
	}
	let temp_10_0 = (mul_((mul_((mod_(a, m)), b)), (add_(a, d))));
	let temp_10_1 = (mul_((mul_((mod_((add_((mul_((mul_((sub_((mod_(b, m)), (mod_(d, m)))), (mul_((mod_(d, m)), d)))), m)), a)), m)), b)), (add_(a, d))));
	assert(eq_(temp_10_0, temp_10_1)) by {
		lemma_mod_mul_vanish(a, mul_(sub_(mod_(b, m), mod_(d, m)), mul_(mod_(d, m), d)), m);
		cong_mul_(mul_(mod_(a, m), b), add_(a, d), mul_(mod_(add_(mul_(mul_(sub_(mod_(b, m), mod_(d, m)), mul_(mod_(d, m), d)), m), a), m), b), add_(a, d));
		lemma_eq_ref(b);
		cong_mul_(mod_(a, m), b, mod_(add_(mul_(mul_(sub_(mod_(b, m), mod_(d, m)), mul_(mod_(d, m), d)), m), a), m), b);
		lemma_eq_ref(add_(a, d));
	}
	let temp_11_0 = (mul_((mul_(d, a)), (mul_(a, (mod_(b, m))))));
	let temp_11_1 = (mul_(d, (mul_(a, (mul_(a, (mod_(b, m))))))));
	assert(eq_(temp_11_0, temp_11_1)) by {
		lemma_mul_assoc(d, a, mul_(a, mod_(b, m)));
		lemma_eq_sym(temp_11_1, temp_11_0);
	}
	let temp_12_0 = (mul_((mul_(d, d)), (mul_(d, a))));
	let temp_12_1 = (mul_((mul_((mul_(d, d)), d)), a));
	assert(eq_(temp_12_0, temp_12_1)) by {
		lemma_mul_assoc(mul_(d, d), d, a);
	}
	let temp_13_0 = (mul_((mul_(b, b)), (mod_((mul_(d, b)), m))));
	let temp_13_1 = (mul_((mul_(b, b)), (mod_((add_((mul_((mul_((mul_((mod_(b, m)), a)), (mul_(b, c)))), m)), (mul_(d, b)))), m))));
	assert(eq_(temp_13_0, temp_13_1)) by {
		lemma_mul_comm(b, b);
		lemma_mod_mul_vanish(mul_(d, b), mul_(mul_(mod_(b, m), a), mul_(b, c)), m);
		cong_mul_(mul_(b, b), mod_(mul_(d, b), m), mul_(b, b), mod_(add_(mul_(mul_(mul_(mod_(b, m), a), mul_(b, c)), m), mul_(d, b)), m));
	}
	let temp_14_0 = (mul_((mul_(c, c)), (mod_((mul_(c, a)), m))));
	let temp_14_1 = (mul_(c, (mul_(c, (mod_((mul_(c, a)), m))))));
	assert(eq_(temp_14_0, temp_14_1)) by {
		lemma_eq_sym(temp_14_1, temp_14_0);
		lemma_mul_assoc(c, c, mod_(mul_(c, a), m));
	}
	let temp_15_0 = (mul_((mul_(a, c)), (mul_((mod_(c, m)), c))));
	let temp_15_1 = (mul_((mul_(a, c)), (mul_((mod_((add_((mul_((mul_((mul_(a, b)), (mul_(a, c)))), m)), c)), m)), c))));
	assert(eq_(temp_15_0, temp_15_1)) by {
		lemma_mod_mul_vanish(c, mul_(mul_(a, b), mul_(a, c)), m);
		cong_mul_(mul_(a, c), mul_(mod_(c, m), c), mul_(a, c), mul_(mod_(add_(mul_(mul_(mul_(a, b), mul_(a, c)), m), c), m), c));
		lemma_eq_ref(c);
		lemma_eq_ref(mul_(a, c));
		cong_mul_(mod_(c, m), c, mod_(add_(mul_(mul_(mul_(a, b), mul_(a, c)), m), c), m), c);
	}
	let temp_16_0 = (mul_((mul_(d, a)), (mul_(d, b))));
	let temp_16_1 = (mul_((mul_((mul_(d, a)), d)), b));
	assert(eq_(temp_16_0, temp_16_1)) by {
		lemma_mul_assoc(mul_(d, a), d, b);
	}
	let temp_17_0 = (mul_((mul_(d, c)), (mod_((mul_((mod_(c, m)), b)), m))));
	let temp_17_1 = (mul_(d, (mul_(c, (mod_((mul_((mod_(c, m)), b)), m))))));
	assert(eq_(temp_17_0, temp_17_1)) by {
		lemma_mul_assoc(d, c, mod_(mul_(mod_(c, m), b), m));
		lemma_eq_sym(temp_17_1, temp_17_0);
	}
	let temp_18_0 = (add_((mul_(d, d)), (mul_(c, c))));
	let temp_18_1 = (add_((mul_(d, d)), (mul_(c, c))));
	assert(eq_(temp_18_0, temp_18_1)) by {
		lemma_eq_ref(temp_18_0);
	}
	let temp_19_0 = (mul_((add_(b, as_elem(50))), (mul_(d, d))));
	let temp_19_1 = (mul_((add_(as_elem(50), b)), (mul_(d, d))));
	assert(eq_(temp_19_0, temp_19_1)) by {
		lemma_add_comm(b, as_elem(50));
		cong_mul_(add_(b, as_elem(50)), mul_(d, d), add_(as_elem(50), b), mul_(d, d));
		lemma_eq_ref(mul_(d, d));
	}
	let temp_20_0 = (mul_((mul_(a, as_elem(58))), (mul_(as_elem(72), d))));
	let temp_20_1 = (mul_((mul_((mul_(a, as_elem(58))), as_elem(72))), d));
	assert(eq_(temp_20_0, temp_20_1)) by {
		lemma_mul_assoc(mul_(a, as_elem(58)), as_elem(72), d);
	}
	let temp_21_0 = (mul_((mul_(d, c)), (sub_((mod_(d, m)), a))));
	let temp_21_1 = (mul_((mul_(d, c)), (sub_((mod_((add_(d, (mul_((mul_((mul_(d, d)), (mul_(c, c)))), m)))), m)), a))));
	assert(eq_(temp_21_0, temp_21_1)) by {
		lemma_mod_mul_vanish(d, mul_(mul_(d, d), mul_(c, c)), m);
		cong_mul_(mul_(d, c), sub_(mod_(d, m), a), mul_(d, c), sub_(mod_(add_(d, mul_(mul_(mul_(d, d), mul_(c, c)), m)), m), a));
		cong_sub_(mod_(d, m), a, mod_(add_(d, mul_(mul_(mul_(d, d), mul_(c, c)), m)), m), a);
		lemma_eq_ref(mul_(d, c));
		lemma_eq_ref(a);
	}
	let temp_22_0 = (mul_((mul_(b, a)), (mul_(c, c))));
	let temp_22_1 = (mul_((mul_((mul_(b, a)), c)), c));
	assert(eq_(temp_22_0, temp_22_1)) by {
		lemma_mul_assoc(mul_(b, a), c, c);
	}
	let temp_23_0 = (mul_((mul_(b, b)), (add_(a, a))));
	let temp_23_1 = (add_((mul_((mul_(b, b)), a)), (mul_((mul_(b, b)), a))));
	assert(eq_(temp_23_0, temp_23_1)) by {
		lemma_mul_dist(mul_(b, b), a, a);
	}
	let temp_24_0 = (mul_((add_(b, (mod_(b, m)))), (mul_(c, (mod_(a, m))))));
	let temp_24_1 = (mul_((mul_((add_(b, (mod_(b, m)))), c)), (mod_(a, m))));
	assert(eq_(temp_24_0, temp_24_1)) by {
		lemma_mul_assoc(add_(b, mod_(b, m)), c, mod_(a, m));
	}
	let temp_25_0 = (sub_((sub_(d, b)), (sub_((mod_(b, m)), (mod_(a, m))))));
	let temp_25_1 = (sub_((sub_(d, b)), (sub_((mod_(b, m)), (mod_((add_((mul_((mul_((add_(c, d)), (mul_(b, (mod_(a, m)))))), m)), a)), m))))));
	assert(eq_(temp_25_0, temp_25_1)) by {
		lemma_mod_mul_vanish(a, mul_(add_(c, d), mul_(b, mod_(a, m))), m);
		cong_sub_(sub_(d, b), sub_(mod_(b, m), mod_(a, m)), sub_(d, b), sub_(mod_(b, m), mod_(add_(mul_(mul_(add_(c, d), mul_(b, mod_(a, m))), m), a), m)));
		cong_sub_(mod_(b, m), mod_(a, m), mod_(b, m), mod_(add_(mul_(mul_(add_(c, d), mul_(b, mod_(a, m))), m), a), m));
		lemma_eq_ref(sub_(d, b));
		lemma_eq_ref(mod_(b, m));
	}
	let temp_26_0 = (mul_((mod_((mul_(c, d)), m)), (add_(b, a))));
	let temp_26_1 = (add_((mul_((mod_((mul_(c, d)), m)), b)), (mul_((mod_((mul_(c, d)), m)), a))));
	assert(eq_(temp_26_0, temp_26_1)) by {
		lemma_mul_dist(mod_(mul_(c, d), m), b, a);
	}
	let temp_27_0 = (mul_((mul_((mod_(as_elem(20), m)), a)), (mul_(a, c))));
	let temp_27_1 = (mul_((mul_((mod_((add_((mul_((mul_((mod_((mul_(d, a)), m)), (sub_(d, c)))), m)), as_elem(20))), m)), a)), (mul_(a, c))));
	assert(eq_(temp_27_0, temp_27_1)) by {
		cong_mul_(mod_(as_elem(20), m), a, mod_(add_(mul_(mul_(mod_(mul_(d, a), m), sub_(d, c)), m), as_elem(20)), m), a);
		lemma_eq_ref(mul_(a, c));
		lemma_eq_ref(a);
		lemma_mod_mul_vanish(as_elem(20), mul_(mod_(mul_(d, a), m), sub_(d, c)), m);
		cong_mul_(mul_(mod_(as_elem(20), m), a), mul_(a, c), mul_(mod_(add_(mul_(mul_(mod_(mul_(d, a), m), sub_(d, c)), m), as_elem(20)), m), a), mul_(a, c));
	}
	let temp_28_0 = (mul_((mul_(c, a)), (mul_(d, b))));
	let temp_28_1 = (mul_((mul_(d, b)), (mul_(c, a))));
	assert(eq_(temp_28_0, temp_28_1)) by {
		lemma_mul_comm(mul_(c, a), mul_(d, b));
	}
	let temp_29_0 = (mod_((mul_((mul_(b, d)), (mul_(as_elem(78), a)))), m));
	let temp_29_1 = (mod_((mul_((mul_(b, d)), (mul_(a, as_elem(78))))), m));
	assert(eq_(temp_29_0, temp_29_1)) by {
		lemma_mul_comm(as_elem(78), a);
		cong_mod_(mul_(mul_(b, d), mul_(as_elem(78), a)), m, mul_(mul_(b, d), mul_(a, as_elem(78))), m);
		lemma_eq_ref(mul_(b, d));
		cong_mul_(mul_(b, d), mul_(as_elem(78), a), mul_(b, d), mul_(a, as_elem(78)));
		lemma_eq_ref(m);
	}
	let temp_30_0 = (mul_((mul_(b, c)), (mod_((add_(a, b)), m))));
	let temp_30_1 = (mul_(b, (mul_(c, (mod_((add_(a, b)), m))))));
	assert(eq_(temp_30_0, temp_30_1)) by {
		lemma_mul_assoc(b, c, mod_(add_(a, b), m));
		lemma_eq_sym(temp_30_1, temp_30_0);
	}
	let temp_31_0 = (mul_((mod_((mul_(c, c)), m)), (sub_(c, c))));
	let temp_31_1 = (mul_((sub_(c, c)), (mod_((mul_(c, c)), m))));
	assert(eq_(temp_31_0, temp_31_1)) by {
		lemma_mul_comm(mod_(mul_(c, c), m), sub_(c, c));
	}
	let temp_32_0 = (mul_((mul_(d, b)), (mul_(a, a))));
	let temp_32_1 = (mul_((mul_(b, d)), (mul_(a, a))));
	assert(eq_(temp_32_0, temp_32_1)) by {
		cong_mul_(mul_(d, b), mul_(a, a), mul_(b, d), mul_(a, a));
		lemma_mul_comm(d, b);
		lemma_mul_comm(a, a);
	}
	let temp_33_0 = (add_((mul_(c, a)), (mul_(c, d))));
	let temp_33_1 = (mul_(c, (add_(a, d))));
	assert(eq_(temp_33_0, temp_33_1)) by {
		lemma_eq_sym(temp_33_1, temp_33_0);
		lemma_mul_dist(c, a, d);
	}
	let temp_34_0 = (mod_((mul_((mul_(a, b)), (mul_(a, a)))), m));
	let temp_34_1 = (mod_((mul_((mul_((mul_(a, b)), a)), a)), m));
	assert(eq_(temp_34_0, temp_34_1)) by {
		lemma_mul_assoc(mul_(a, b), a, a);
		cong_mod_(mul_(mul_(a, b), mul_(a, a)), m, mul_(mul_(mul_(a, b), a), a), m);
		lemma_eq_ref(m);
	}
	let temp_35_0 = (add_((sub_(b, b)), (mul_(a, b))));
	let temp_35_1 = (add_((mul_(a, b)), (sub_(b, b))));
	assert(eq_(temp_35_0, temp_35_1)) by {
		lemma_add_comm(sub_(b, b), mul_(a, b));
	}
	let temp_36_0 = (mul_((add_(d, c)), (add_(c, a))));
	let temp_36_1 = (mul_((add_(c, a)), (add_(d, c))));
	assert(eq_(temp_36_0, temp_36_1)) by {
		lemma_mul_comm(add_(d, c), add_(c, a));
	}
	let temp_37_0 = (mul_((sub_(a, b)), (mul_(d, b))));
	let temp_37_1 = (mul_((sub_(a, b)), (mul_(b, d))));
	assert(eq_(temp_37_0, temp_37_1)) by {
		cong_mul_(sub_(a, b), mul_(d, b), sub_(a, b), mul_(b, d));
		lemma_mul_comm(d, b);
		lemma_eq_ref(sub_(a, b));
	}
	let temp_38_0 = (mod_((mul_((sub_(c, a)), (mul_(d, (mod_(c, m)))))), m));
	let temp_38_1 = (mod_((mul_((sub_(c, a)), (mul_((mod_(c, m)), d)))), m));
	assert(eq_(temp_38_0, temp_38_1)) by {
		lemma_mul_comm(d, mod_(c, m));
		cong_mod_(mul_(sub_(c, a), mul_(d, mod_(c, m))), m, mul_(sub_(c, a), mul_(mod_(c, m), d)), m);
		lemma_eq_ref(sub_(c, a));
		cong_mul_(sub_(c, a), mul_(d, mod_(c, m)), sub_(c, a), mul_(mod_(c, m), d));
		lemma_eq_ref(m);
	}
	let temp_39_0 = (mul_((mod_((mul_(a, d)), m)), (add_(c, (mod_(a, m))))));
	let temp_39_1 = (mul_((mod_((mul_(a, d)), m)), (add_((mod_(a, m)), c))));
	assert(eq_(temp_39_0, temp_39_1)) by {
		lemma_add_comm(c, mod_(a, m));
		cong_mul_(mod_(mul_(a, d), m), add_(c, mod_(a, m)), mod_(mul_(a, d), m), add_(mod_(a, m), c));
		lemma_eq_ref(mod_(mul_(a, d), m));
	}
	let temp_40_0 = (mul_((mul_(a, d)), (sub_(b, d))));
	let temp_40_1 = (mul_((sub_(b, d)), (mul_(a, d))));
	assert(eq_(temp_40_0, temp_40_1)) by {
		lemma_mul_comm(mul_(a, d), sub_(b, d));
	}
	let temp_41_0 = (mul_((mul_(b, b)), (mul_(c, (mod_(c, m))))));
	let temp_41_1 = (mul_((mul_(b, b)), (mul_((mod_(c, m)), c))));
	assert(eq_(temp_41_0, temp_41_1)) by {
		cong_mul_(mul_(b, b), mul_(c, mod_(c, m)), mul_(b, b), mul_(mod_(c, m), c));
		lemma_mul_comm(b, b);
		lemma_mul_comm(c, mod_(c, m));
	}
	let temp_42_0 = (mul_((mul_(c, a)), (mul_(d, b))));
	let temp_42_1 = (mul_((mul_(a, c)), (mul_(d, b))));
	assert(eq_(temp_42_0, temp_42_1)) by {
		cong_mul_(mul_(c, a), mul_(d, b), mul_(a, c), mul_(d, b));
		lemma_mul_comm(c, a);
		lemma_eq_ref(mul_(d, b));
	}
	let temp_43_0 = (mul_((add_(as_elem(45), b)), (mul_(as_elem(46), d))));
	let temp_43_1 = (mul_((mul_(as_elem(46), d)), (add_(as_elem(45), b))));
	assert(eq_(temp_43_0, temp_43_1)) by {
		lemma_mul_comm(add_(as_elem(45), b), mul_(as_elem(46), d));
	}
	let temp_44_0 = (mul_((mul_(c, a)), d));
	let temp_44_1 = (mul_((mul_(a, c)), d));
	assert(eq_(temp_44_0, temp_44_1)) by {
		lemma_eq_ref(d);
		cong_mul_(mul_(c, a), d, mul_(a, c), d);
		lemma_mul_comm(c, a);
	}
	let temp_45_0 = (mul_((mul_(c, c)), (mul_(as_elem(49), c))));
	let temp_45_1 = (mul_((mul_((mul_(c, c)), as_elem(49))), c));
	assert(eq_(temp_45_0, temp_45_1)) by {
		lemma_mul_assoc(mul_(c, c), as_elem(49), c);
	}
	let temp_46_0 = (mul_((mul_(a, a)), (sub_(c, a))));
	let temp_46_1 = (mul_(a, (mul_(a, (sub_(c, a))))));
	assert(eq_(temp_46_0, temp_46_1)) by {
		lemma_eq_sym(temp_46_1, temp_46_0);
		lemma_mul_assoc(a, a, sub_(c, a));
	}
	let temp_47_0 = (mul_((mul_(b, b)), (add_(d, a))));
	let temp_47_1 = (add_((mul_((mul_(b, b)), d)), (mul_((mul_(b, b)), a))));
	assert(eq_(temp_47_0, temp_47_1)) by {
		lemma_mul_dist(mul_(b, b), d, a);
	}
	let temp_48_0 = (mul_((mul_((mod_(c, m)), d)), (mul_(c, a))));
	let temp_48_1 = (mul_((mod_(c, m)), (mul_(d, (mul_(c, a))))));
	assert(eq_(temp_48_0, temp_48_1)) by {
		lemma_mul_assoc(mod_(c, m), d, mul_(c, a));
		lemma_eq_sym(temp_48_1, temp_48_0);
	}
	let temp_49_0 = (mul_((mul_(a, c)), (mul_(c, a))));
	let temp_49_1 = (mul_(a, (mul_(c, (mul_(c, a))))));
	assert(eq_(temp_49_0, temp_49_1)) by {
		lemma_eq_sym(temp_49_1, temp_49_0);
		lemma_mul_assoc(a, c, mul_(c, a));
	}
	let temp_50_0 = (sub_((mul_(b, c)), (mul_(b, b))));
	let temp_50_1 = (sub_((mul_(c, b)), (mul_(b, b))));
	assert(eq_(temp_50_0, temp_50_1)) by {
		cong_sub_(mul_(b, c), mul_(b, b), mul_(c, b), mul_(b, b));
		lemma_mul_comm(b, c);
		lemma_mul_comm(b, b);
	}
	let temp_51_0 = (add_((mul_(a, a)), (mod_((mul_(c, a)), m))));
	let temp_51_1 = (add_((mul_(a, a)), (mod_((mul_(a, c)), m))));
	assert(eq_(temp_51_0, temp_51_1)) by {
		lemma_mul_comm(c, a);
		cong_add_(mul_(a, a), mod_(mul_(c, a), m), mul_(a, a), mod_(mul_(a, c), m));
		lemma_eq_ref(mul_(a, a));
		lemma_eq_ref(m);
		cong_mod_(mul_(c, a), m, mul_(a, c), m);
	}
	let temp_52_0 = (mod_((add_((sub_(b, c)), (mul_(d, c)))), m));
	let temp_52_1 = (mod_((add_((add_((sub_(b, c)), (mul_(d, c)))), (mul_((mul_((sub_(d, b)), (mul_((mod_(a, m)), d)))), m)))), m));
	assert(eq_(temp_52_0, temp_52_1)) by {
		lemma_mod_mul_vanish(add_(sub_(b, c), mul_(d, c)), mul_(sub_(d, b), mul_(mod_(a, m), d)), m);
	}
	let temp_53_0 = (mul_((mul_(a, a)), (mul_(c, (mod_(a, m))))));
	let temp_53_1 = (mul_(a, (mul_(a, (mul_(c, (mod_(a, m))))))));
	assert(eq_(temp_53_0, temp_53_1)) by {
		lemma_eq_sym(temp_53_1, temp_53_0);
		lemma_mul_assoc(a, a, mul_(c, mod_(a, m)));
	}
	let temp_54_0 = (mul_((mul_(a, a)), (mul_(a, (mod_(d, m))))));
	let temp_54_1 = (mul_((mul_(a, a)), (mul_(a, (mod_((sub_(d, (mul_((mul_((mul_(c, (mod_(b, m)))), (mul_(c, c)))), m)))), m))))));
	assert(eq_(temp_54_0, temp_54_1)) by {
		cong_mul_(a, mod_(d, m), a, mod_(sub_(d, mul_(mul_(mul_(c, mod_(b, m)), mul_(c, c)), m)), m));
		lemma_eq_ref(a);
		lemma_mul_comm(a, a);
		lemma_mod_mul_vanish(d, mul_(mul_(c, mod_(b, m)), mul_(c, c)), m);
		cong_mul_(mul_(a, a), mul_(a, mod_(d, m)), mul_(a, a), mul_(a, mod_(sub_(d, mul_(mul_(mul_(c, mod_(b, m)), mul_(c, c)), m)), m)));
	}
	let temp_55_0 = (mul_((mul_(b, b)), (mul_(a, a))));
	let temp_55_1 = (mul_((mul_(b, b)), (mul_(a, a))));
	assert(eq_(temp_55_0, temp_55_1)) by {
		lemma_eq_ref(temp_55_0);
	}
	let temp_56_0 = (mul_((mod_((mul_(c, d)), m)), (add_((mod_(a, m)), d))));
	let temp_56_1 = (mul_((mod_((mul_(c, d)), m)), (add_(d, (mod_(a, m))))));
	assert(eq_(temp_56_0, temp_56_1)) by {
		lemma_add_comm(mod_(a, m), d);
		cong_mul_(mod_(mul_(c, d), m), add_(mod_(a, m), d), mod_(mul_(c, d), m), add_(d, mod_(a, m)));
		lemma_eq_ref(mod_(mul_(c, d), m));
	}
	let temp_57_0 = (mul_((mul_(c, d)), (mul_(a, c))));
	let temp_57_1 = (mul_((mul_(a, c)), (mul_(c, d))));
	assert(eq_(temp_57_0, temp_57_1)) by {
		lemma_mul_comm(mul_(c, d), mul_(a, c));
	}
	let temp_58_0 = (mod_((sub_((mul_(b, d)), (mul_((mod_(a, m)), d)))), m));
	let temp_58_1 = (mod_((sub_((mul_(b, d)), (mul_((mod_((add_(a, (mul_((mul_((mul_(d, d)), (mul_(as_elem(28), (mod_(c, m)))))), m)))), m)), d)))), m));
	assert(eq_(temp_58_0, temp_58_1)) by {
		cong_mod_(sub_(mul_(b, d), mul_(mod_(a, m), d)), m, sub_(mul_(b, d), mul_(mod_(add_(a, mul_(mul_(mul_(d, d), mul_(as_elem(28), mod_(c, m))), m)), m), d)), m);
		lemma_mod_mul_vanish(a, mul_(mul_(d, d), mul_(as_elem(28), mod_(c, m))), m);
		cong_sub_(mul_(b, d), mul_(mod_(a, m), d), mul_(b, d), mul_(mod_(add_(a, mul_(mul_(mul_(d, d), mul_(as_elem(28), mod_(c, m))), m)), m), d));
		lemma_eq_ref(d);
		lemma_eq_ref(mul_(b, d));
		cong_mul_(mod_(a, m), d, mod_(add_(a, mul_(mul_(mul_(d, d), mul_(as_elem(28), mod_(c, m))), m)), m), d);
		lemma_eq_ref(m);
	}
	let temp_59_0 = (mod_((mul_((mul_(c, d)), (mul_(b, a)))), m));
	let temp_59_1 = (mod_((mul_(c, (mul_(d, (mul_(b, a)))))), m));
	assert(eq_(temp_59_0, temp_59_1)) by {
		lemma_mul_assoc(c, d, mul_(b, a));
		cong_mod_(mul_(mul_(c, d), mul_(b, a)), m, mul_(c, mul_(d, mul_(b, a))), m);
		lemma_eq_sym(mul_(c, mul_(d, mul_(b, a))), mul_(mul_(c, d), mul_(b, a)));
		lemma_eq_ref(m);
	}
	let temp_60_0 = (mul_((mul_(a, as_elem(38))), (mul_(c, b))));
	let temp_60_1 = (mul_((mul_(a, as_elem(38))), (mul_(b, c))));
	assert(eq_(temp_60_0, temp_60_1)) by {
		lemma_mul_comm(c, b);
		cong_mul_(mul_(a, as_elem(38)), mul_(c, b), mul_(a, as_elem(38)), mul_(b, c));
		lemma_eq_ref(mul_(a, as_elem(38)));
	}
	let temp_61_0 = (sub_((sub_(a, c)), (mod_((mul_(b, d)), m))));
	let temp_61_1 = (sub_((sub_(a, c)), (mod_((add_((mul_((mul_((mul_(d, b)), (sub_(b, c)))), m)), (mul_(b, d)))), m))));
	assert(eq_(temp_61_0, temp_61_1)) by {
		lemma_mod_mul_vanish(mul_(b, d), mul_(mul_(d, b), sub_(b, c)), m);
		cong_sub_(sub_(a, c), mod_(mul_(b, d), m), sub_(a, c), mod_(add_(mul_(mul_(mul_(d, b), sub_(b, c)), m), mul_(b, d)), m));
		lemma_eq_ref(sub_(a, c));
	}
	let temp_62_0 = (sub_((mul_(b, b)), (mul_((mod_(c, m)), d))));
	let temp_62_1 = (sub_((mul_(b, b)), (mul_((mod_(c, m)), d))));
	assert(eq_(temp_62_0, temp_62_1)) by {
		lemma_eq_ref(temp_62_0);
	}
	let temp_63_0 = (mul_((mul_(d, d)), (mul_(c, b))));
	let temp_63_1 = (mul_((mul_((mul_(d, d)), c)), b));
	assert(eq_(temp_63_0, temp_63_1)) by {
		lemma_mul_assoc(mul_(d, d), c, b);
	}
	let temp_64_0 = (sub_((mul_(b, a)), (mul_(b, (mod_(a, m))))));
	let temp_64_1 = (sub_((mul_(a, b)), (mul_(b, (mod_(a, m))))));
	assert(eq_(temp_64_0, temp_64_1)) by {
		cong_sub_(mul_(b, a), mul_(b, mod_(a, m)), mul_(a, b), mul_(b, mod_(a, m)));
		lemma_mul_comm(b, a);
		lemma_eq_ref(mul_(b, mod_(a, m)));
	}
	let temp_65_0 = (mul_((mul_(b, c)), (mul_(b, c))));
	let temp_65_1 = (mul_((mul_(c, b)), (mul_(b, c))));
	assert(eq_(temp_65_0, temp_65_1)) by {
		cong_mul_(mul_(b, c), mul_(b, c), mul_(c, b), mul_(b, c));
		lemma_mul_comm(b, c);
		lemma_eq_ref(mul_(b, c));
	}
	let temp_66_0 = (mul_((mul_(c, a)), (add_(b, (mod_(c, m))))));
	let temp_66_1 = (mul_(c, (mul_(a, (add_(b, (mod_(c, m))))))));
	assert(eq_(temp_66_0, temp_66_1)) by {
		lemma_mul_assoc(c, a, add_(b, mod_(c, m)));
		lemma_eq_sym(temp_66_1, temp_66_0);
	}
	let temp_67_0 = (mul_((mod_(a, m)), (mul_(d, d))));
	let temp_67_1 = (mul_((mod_((sub_(a, (mul_((mul_((mul_(as_elem(85), c)), (mul_(a, b)))), m)))), m)), (mul_(d, d))));
	assert(eq_(temp_67_0, temp_67_1)) by {
		lemma_mul_comm(d, d);
		lemma_mod_mul_vanish(a, mul_(mul_(as_elem(85), c), mul_(a, b)), m);
		cong_mul_(mod_(a, m), mul_(d, d), mod_(sub_(a, mul_(mul_(mul_(as_elem(85), c), mul_(a, b)), m)), m), mul_(d, d));
	}
	let temp_68_0 = (mod_((mul_((sub_(b, d)), (mul_(d, b)))), m));
	let temp_68_1 = (mod_((mul_((mul_((sub_(b, d)), d)), b)), m));
	assert(eq_(temp_68_0, temp_68_1)) by {
		lemma_mul_assoc(sub_(b, d), d, b);
		cong_mod_(mul_(sub_(b, d), mul_(d, b)), m, mul_(mul_(sub_(b, d), d), b), m);
		lemma_eq_ref(m);
	}
	let temp_69_0 = (mul_((mod_((add_(c, a)), m)), (add_(c, a))));
	let temp_69_1 = (mul_((mod_((add_(c, a)), m)), (add_(a, c))));
	assert(eq_(temp_69_0, temp_69_1)) by {
		lemma_eq_ref(mod_(add_(c, a), m));
		cong_mul_(mod_(add_(c, a), m), add_(c, a), mod_(add_(c, a), m), add_(a, c));
		lemma_add_comm(c, a);
	}
	let temp_70_0 = (mul_((mul_(d, d)), (mul_(d, a))));
	let temp_70_1 = (mul_((mul_(d, d)), (mul_(a, d))));
	assert(eq_(temp_70_0, temp_70_1)) by {
		cong_mul_(mul_(d, d), mul_(d, a), mul_(d, d), mul_(a, d));
		lemma_mul_comm(d, d);
		lemma_mul_comm(d, a);
	}
	let temp_71_0 = (mul_((sub_(c, b)), (mul_(b, d))));
	let temp_71_1 = (mul_((mul_(b, d)), (sub_(c, b))));
	assert(eq_(temp_71_0, temp_71_1)) by {
		lemma_mul_comm(sub_(c, b), mul_(b, d));
	}
	let temp_72_0 = (mul_((mul_(b, b)), (mul_(a, c))));
	let temp_72_1 = (mul_((mul_(b, b)), (mul_(c, a))));
	assert(eq_(temp_72_0, temp_72_1)) by {
		cong_mul_(mul_(b, b), mul_(a, c), mul_(b, b), mul_(c, a));
		lemma_mul_comm(b, b);
		lemma_mul_comm(a, c);
	}
	let temp_73_0 = (mul_((mul_(d, b)), (mul_(c, c))));
	let temp_73_1 = (mul_((mul_(b, d)), (mul_(c, c))));
	assert(eq_(temp_73_0, temp_73_1)) by {
		cong_mul_(mul_(d, b), mul_(c, c), mul_(b, d), mul_(c, c));
		lemma_mul_comm(d, b);
		lemma_mul_comm(c, c);
	}
	let temp_74_0 = (mul_((sub_(c, (mod_(a, m)))), (mul_(a, c))));
	let temp_74_1 = (mul_((sub_(c, (mod_(a, m)))), (mul_(c, a))));
	assert(eq_(temp_74_0, temp_74_1)) by {
		cong_mul_(sub_(c, mod_(a, m)), mul_(a, c), sub_(c, mod_(a, m)), mul_(c, a));
		lemma_mul_comm(a, c);
		lemma_eq_ref(sub_(c, mod_(a, m)));
	}
	let temp_75_0 = (mod_((mul_((mul_(a, d)), (mul_(c, d)))), m));
	let temp_75_1 = (mod_((mul_((mul_(c, d)), (mul_(a, d)))), m));
	assert(eq_(temp_75_0, temp_75_1)) by {
		lemma_mul_comm(mul_(a, d), mul_(c, d));
		cong_mod_(mul_(mul_(a, d), mul_(c, d)), m, mul_(mul_(c, d), mul_(a, d)), m);
		lemma_eq_ref(m);
	}
	let temp_76_0 = (mul_((add_(d, b)), (mul_(b, (mod_(b, m))))));
	let temp_76_1 = (mul_((mul_(b, (mod_(b, m)))), (add_(d, b))));
	assert(eq_(temp_76_0, temp_76_1)) by {
		lemma_mul_comm(add_(d, b), mul_(b, mod_(b, m)));
	}
	let temp_77_0 = (mul_((mul_(a, c)), (add_(c, a))));
	let temp_77_1 = (add_((mul_((mul_(a, c)), c)), (mul_((mul_(a, c)), a))));
	assert(eq_(temp_77_0, temp_77_1)) by {
		lemma_mul_dist(mul_(a, c), c, a);
	}
	let temp_78_0 = (mul_((mul_(d, c)), (mul_(b, (mod_(b, m))))));
	let temp_78_1 = (mul_((mul_(d, c)), (mul_(b, (mod_((add_((mul_((mul_((mul_(a, c)), (mul_(b, c)))), m)), b)), m))))));
	assert(eq_(temp_78_0, temp_78_1)) by {
		lemma_mod_mul_vanish(b, mul_(mul_(a, c), mul_(b, c)), m);
		cong_mul_(mul_(d, c), mul_(b, mod_(b, m)), mul_(d, c), mul_(b, mod_(add_(mul_(mul_(mul_(a, c), mul_(b, c)), m), b), m)));
		lemma_eq_ref(b);
		lemma_eq_ref(mul_(d, c));
		cong_mul_(b, mod_(b, m), b, mod_(add_(mul_(mul_(mul_(a, c), mul_(b, c)), m), b), m));
	}
	let temp_79_0 = (mul_((mul_(c, d)), (mul_(a, c))));
	let temp_79_1 = (mul_((mul_(a, c)), (mul_(c, d))));
	assert(eq_(temp_79_0, temp_79_1)) by {
		lemma_mul_comm(mul_(c, d), mul_(a, c));
	}
	let temp_80_0 = (mul_((add_(as_elem(88), (mod_(d, m)))), (mul_(c, b))));
	let temp_80_1 = (mul_((mul_(c, b)), (add_(as_elem(88), (mod_(d, m))))));
	assert(eq_(temp_80_0, temp_80_1)) by {
		lemma_mul_comm(add_(as_elem(88), mod_(d, m)), mul_(c, b));
	}
	let temp_81_0 = (mul_((mul_(a, (mod_(c, m)))), (mod_((mul_(b, c)), m))));
	let temp_81_1 = (mul_(a, (mul_((mod_(c, m)), (mod_((mul_(b, c)), m))))));
	assert(eq_(temp_81_0, temp_81_1)) by {
		lemma_mul_assoc(a, mod_(c, m), mod_(mul_(b, c), m));
		lemma_eq_sym(temp_81_1, temp_81_0);
	}
	let temp_82_0 = (sub_((mul_((mod_(b, m)), d)), (mod_((mul_(d, a)), m))));
	let temp_82_1 = (sub_((mul_(d, (mod_(b, m)))), (mod_((mul_(d, a)), m))));
	assert(eq_(temp_82_0, temp_82_1)) by {
		lemma_mul_comm(mod_(b, m), d);
		cong_sub_(mul_(mod_(b, m), d), mod_(mul_(d, a), m), mul_(d, mod_(b, m)), mod_(mul_(d, a), m));
		lemma_eq_ref(mod_(mul_(d, a), m));
	}
	let temp_83_0 = (mul_((mul_(c, d)), (mul_(c, b))));
	let temp_83_1 = (mul_((mul_(c, b)), (mul_(c, d))));
	assert(eq_(temp_83_0, temp_83_1)) by {
		lemma_mul_comm(mul_(c, d), mul_(c, b));
	}
	let temp_84_0 = (mul_((add_(a, d)), (mul_(d, (mod_(c, m))))));
	let temp_84_1 = (add_((mul_(a, (mul_(d, (mod_(c, m)))))), (mul_(d, (mul_(d, (mod_(c, m))))))));
	assert(eq_(temp_84_0, temp_84_1)) by {
		lemma_mul_dist(a, d, mul_(d, mod_(c, m)));
	}
	let temp_85_0 = (sub_((mul_(b, d)), (mul_(d, (mod_(c, m))))));
	let temp_85_1 = (sub_((mul_(d, b)), (mul_(d, (mod_(c, m))))));
	assert(eq_(temp_85_0, temp_85_1)) by {
		lemma_mul_comm(b, d);
		cong_sub_(mul_(b, d), mul_(d, mod_(c, m)), mul_(d, b), mul_(d, mod_(c, m)));
		lemma_eq_ref(mul_(d, mod_(c, m)));
	}
	let temp_86_0 = (mul_((sub_(b, c)), (add_(a, c))));
	let temp_86_1 = (mul_((sub_(b, c)), (add_(c, a))));
	assert(eq_(temp_86_0, temp_86_1)) by {
		cong_mul_(sub_(b, c), add_(a, c), sub_(b, c), add_(c, a));
		lemma_add_comm(a, c);
		lemma_eq_ref(sub_(b, c));
	}
	let temp_87_0 = (mod_((add_((mul_(d, c)), (mul_(c, b)))), m));
	let temp_87_1 = (mod_((sub_((add_((mul_(d, c)), (mul_(c, b)))), (mul_((mul_((mul_(d, b)), c)), m)))), m));
	assert(eq_(temp_87_0, temp_87_1)) by {
		lemma_mod_mul_vanish(add_(mul_(d, c), mul_(c, b)), mul_(mul_(d, b), c), m);
	}
	let temp_88_0 = (add_((mul_(d, c)), (mul_(c, d))));
	let temp_88_1 = (add_((mul_(c, d)), (mul_(c, d))));
	assert(eq_(temp_88_0, temp_88_1)) by {
		cong_add_(mul_(d, c), mul_(c, d), mul_(c, d), mul_(c, d));
		lemma_mul_comm(d, c);
		lemma_eq_ref(mul_(c, d));
	}
	let temp_89_0 = (mul_((mul_((mod_(d, m)), b)), (mul_((mod_(b, m)), d))));
	let temp_89_1 = (mul_((mul_((mul_((mod_(d, m)), b)), (mod_(b, m)))), d));
	assert(eq_(temp_89_0, temp_89_1)) by {
		lemma_mul_assoc(mul_(mod_(d, m), b), mod_(b, m), d);
	}
	let temp_90_0 = (mul_((mul_(d, d)), (sub_(b, c))));
	let temp_90_1 = (mul_((sub_(b, c)), (mul_(d, d))));
	assert(eq_(temp_90_0, temp_90_1)) by {
		lemma_mul_comm(mul_(d, d), sub_(b, c));
	}
	let temp_91_0 = (add_((mul_(c, c)), (mul_(a, a))));
	let temp_91_1 = (add_((mul_(c, c)), (mul_(a, a))));
	assert(eq_(temp_91_0, temp_91_1)) by {
		lemma_eq_ref(temp_91_0);
	}
	let temp_92_0 = (sub_((mul_(a, b)), (mul_(a, a))));
	let temp_92_1 = (sub_((mul_(b, a)), (mul_(a, a))));
	assert(eq_(temp_92_0, temp_92_1)) by {
		cong_sub_(mul_(a, b), mul_(a, a), mul_(b, a), mul_(a, a));
		lemma_mul_comm(a, b);
		lemma_mul_comm(a, a);
	}

}

} // verus!