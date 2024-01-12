use builtin_macros::*;
// use builtin::*;
mod nl_basics;
use crate::nl_basics::*;
verus! {

pub proof fn free_0(a: Elem, b: Elem, c: Elem, d: Elem, m: Elem)
{
	let temp_0_0 = (sub_((mod_((mul_(a, as_elem(74))), m)), (mod_((sub_(c, b)), m))));
	let temp_0_1 = (sub_((mod_((mul_(a, as_elem(74))), m)), (mod_((add_((sub_(c, b)), (mul_((mul_((sub_(a, c)), (mul_(b, d)))), m)))), m))));
	assert(eq_(temp_0_0, temp_0_1)) by {
		lemma_mod_mul_vanish(sub_(c, b), mul_(sub_(a, c), mul_(b, d)), m);
		cong_sub_(mod_(mul_(a, as_elem(74)), m), mod_(sub_(c, b), m), mod_(mul_(a, as_elem(74)), m), mod_(add_(sub_(c, b), mul_(mul_(sub_(a, c), mul_(b, d)), m)), m));
		lemma_eq_ref(mod_(mul_(a, as_elem(74)), m));
	}
	let temp_1_0 = (mul_((mul_(b, b)), (add_(c, b))));
	let temp_1_1 = (mul_((mul_(b, b)), (add_(b, c))));
	assert(eq_(temp_1_0, temp_1_1)) by {
		cong_mul_(mul_(b, b), add_(c, b), mul_(b, b), add_(b, c));
		lemma_add_comm(c, b);
		lemma_mul_comm(b, b);
	}
	let temp_2_0 = (mul_((mul_(b, b)), (mul_(b, d))));
	let temp_2_1 = (mul_((mul_(b, b)), (mul_(d, b))));
	assert(eq_(temp_2_0, temp_2_1)) by {
		cong_mul_(mul_(b, b), mul_(b, d), mul_(b, b), mul_(d, b));
		lemma_mul_comm(b, b);
		lemma_mul_comm(b, d);
	}
	let temp_3_0 = (sub_((mul_(c, b)), (mul_(a, c))));
	let temp_3_1 = (sub_((mul_(c, b)), (mul_(c, a))));
	assert(eq_(temp_3_0, temp_3_1)) by {
		cong_sub_(mul_(c, b), mul_(a, c), mul_(c, b), mul_(c, a));
		lemma_mul_comm(a, c);
		lemma_eq_ref(mul_(c, b));
	}
	let temp_4_0 = (mul_((mul_(b, b)), (mul_(b, b))));
	let temp_4_1 = (mul_((mul_((mul_(b, b)), b)), b));
	assert(eq_(temp_4_0, temp_4_1)) by {
		lemma_mul_assoc(mul_(b, b), b, b);
	}
	let temp_5_0 = (mul_((mul_(a, b)), (mod_((mul_((mod_(a, m)), c)), m))));
	let temp_5_1 = (mul_(a, (mul_(b, (mod_((mul_((mod_(a, m)), c)), m))))));
	assert(eq_(temp_5_0, temp_5_1)) by {
		lemma_mul_assoc(a, b, mod_(mul_(mod_(a, m), c), m));
		lemma_eq_sym(temp_5_1, temp_5_0);
	}
	let temp_6_0 = (mul_((mul_(c, d)), (mul_(d, as_elem(40)))));
	let temp_6_1 = (mul_((mul_(c, d)), (mul_(as_elem(40), d))));
	assert(eq_(temp_6_0, temp_6_1)) by {
		cong_mul_(mul_(c, d), mul_(d, as_elem(40)), mul_(c, d), mul_(as_elem(40), d));
		lemma_mul_comm(d, as_elem(40));
		lemma_eq_ref(mul_(c, d));
	}
	let temp_7_0 = (sub_((mul_(a, d)), (add_(d, c))));
	let temp_7_1 = (sub_((mul_(a, d)), (add_(c, d))));
	assert(eq_(temp_7_0, temp_7_1)) by {
		cong_sub_(mul_(a, d), add_(d, c), mul_(a, d), add_(c, d));
		lemma_add_comm(d, c);
		lemma_eq_ref(mul_(a, d));
	}
	let temp_8_0 = (mul_((mul_(a, d)), (mul_(a, d))));
	let temp_8_1 = (mul_((mul_(a, d)), (mul_(a, d))));
	assert(eq_(temp_8_0, temp_8_1)) by {
		lemma_eq_ref(temp_8_0);
	}
	let temp_9_0 = (mul_((sub_(a, (mod_(a, m)))), (mul_(d, b))));
	let temp_9_1 = (mul_((sub_(a, (mod_((sub_(a, (mul_((mul_((sub_(b, c)), (mul_(a, b)))), m)))), m)))), (mul_(d, b))));
	assert(eq_(temp_9_0, temp_9_1)) by {
		cong_sub_(a, mod_(a, m), a, mod_(sub_(a, mul_(mul_(sub_(b, c), mul_(a, b)), m)), m));
		lemma_eq_ref(mul_(d, b));
		lemma_mod_mul_vanish(a, mul_(sub_(b, c), mul_(a, b)), m);
		cong_mul_(sub_(a, mod_(a, m)), mul_(d, b), sub_(a, mod_(sub_(a, mul_(mul_(sub_(b, c), mul_(a, b)), m)), m)), mul_(d, b));
		lemma_eq_ref(a);
	}
	let temp_10_0 = (mul_((add_(a, a)), (sub_(as_elem(12), d))));
	let temp_10_1 = (mul_((sub_(as_elem(12), d)), (add_(a, a))));
	assert(eq_(temp_10_0, temp_10_1)) by {
		lemma_mul_comm(add_(a, a), sub_(as_elem(12), d));
	}
	let temp_11_0 = (mod_((sub_((mul_(c, c)), (mul_(c, (mod_(b, m)))))), m));
	let temp_11_1 = (mod_((sub_((mul_(c, c)), (mul_(c, (mod_((sub_(b, (mul_((mul_((mul_(b, a)), (mod_((mul_(d, a)), m)))), m)))), m)))))), m));
	assert(eq_(temp_11_0, temp_11_1)) by {
		lemma_mul_comm(c, c);
		lemma_mod_mul_vanish(b, mul_(mul_(b, a), mod_(mul_(d, a), m)), m);
		cong_mod_(sub_(mul_(c, c), mul_(c, mod_(b, m))), m, sub_(mul_(c, c), mul_(c, mod_(sub_(b, mul_(mul_(mul_(b, a), mod_(mul_(d, a), m)), m)), m))), m);
		cong_sub_(mul_(c, c), mul_(c, mod_(b, m)), mul_(c, c), mul_(c, mod_(sub_(b, mul_(mul_(mul_(b, a), mod_(mul_(d, a), m)), m)), m)));
		lemma_eq_ref(m);
		lemma_eq_ref(c);
		cong_mul_(c, mod_(b, m), c, mod_(sub_(b, mul_(mul_(mul_(b, a), mod_(mul_(d, a), m)), m)), m));
	}
	let temp_12_0 = (add_((mul_(b, c)), (mul_(c, b))));
	let temp_12_1 = (add_((mul_(b, c)), (mul_(b, c))));
	assert(eq_(temp_12_0, temp_12_1)) by {
		cong_add_(mul_(b, c), mul_(c, b), mul_(b, c), mul_(b, c));
		lemma_mul_comm(c, b);
		lemma_eq_ref(mul_(b, c));
	}
	let temp_13_0 = (mul_((mul_(b, c)), (mul_(a, d))));
	let temp_13_1 = (mul_((mul_((mul_(b, c)), a)), d));
	assert(eq_(temp_13_0, temp_13_1)) by {
		lemma_mul_assoc(mul_(b, c), a, d);
	}
	let temp_14_0 = (mul_((mul_(d, a)), (mod_((mul_(b, (mod_(a, m)))), m))));
	let temp_14_1 = (mul_((mul_(d, a)), (mod_((mul_(b, (mod_((add_(a, (mul_((mul_((mul_(d, d)), (mul_(d, c)))), m)))), m)))), m))));
	assert(eq_(temp_14_0, temp_14_1)) by {
		lemma_mod_mul_vanish(a, mul_(mul_(d, d), mul_(d, c)), m);
		cong_mul_(mul_(d, a), mod_(mul_(b, mod_(a, m)), m), mul_(d, a), mod_(mul_(b, mod_(add_(a, mul_(mul_(mul_(d, d), mul_(d, c)), m)), m)), m));
		cong_mod_(mul_(b, mod_(a, m)), m, mul_(b, mod_(add_(a, mul_(mul_(mul_(d, d), mul_(d, c)), m)), m)), m);
		lemma_eq_ref(mul_(d, a));
		lemma_eq_ref(b);
		cong_mul_(b, mod_(a, m), b, mod_(add_(a, mul_(mul_(mul_(d, d), mul_(d, c)), m)), m));
		lemma_eq_ref(m);
	}
	let temp_15_0 = (mul_((mul_((mod_(b, m)), c)), (mul_(a, c))));
	let temp_15_1 = (mul_((mul_(c, (mod_(b, m)))), (mul_(a, c))));
	assert(eq_(temp_15_0, temp_15_1)) by {
		lemma_mul_comm(mod_(b, m), c);
		cong_mul_(mul_(mod_(b, m), c), mul_(a, c), mul_(c, mod_(b, m)), mul_(a, c));
		lemma_eq_ref(mul_(a, c));
	}
	let temp_16_0 = (mul_((sub_(b, d)), (mul_(b, c))));
	let temp_16_1 = (mul_((mul_((sub_(b, d)), b)), c));
	assert(eq_(temp_16_0, temp_16_1)) by {
		lemma_mul_assoc(sub_(b, d), b, c);
	}
	let temp_17_0 = (mod_((mul_((mul_(d, a)), (mul_(a, b)))), m));
	let temp_17_1 = (mod_((mul_((mul_((mul_(d, a)), a)), b)), m));
	assert(eq_(temp_17_0, temp_17_1)) by {
		lemma_mul_assoc(mul_(d, a), a, b);
		cong_mod_(mul_(mul_(d, a), mul_(a, b)), m, mul_(mul_(mul_(d, a), a), b), m);
		lemma_eq_ref(m);
	}
	let temp_18_0 = (mul_((mul_(as_elem(27), a)), (mul_(c, b))));
	let temp_18_1 = (mul_(as_elem(27), (mul_(a, (mul_(c, b))))));
	assert(eq_(temp_18_0, temp_18_1)) by {
		lemma_mul_assoc(as_elem(27), a, mul_(c, b));
		lemma_eq_sym(temp_18_1, temp_18_0);
	}
	let temp_19_0 = (mul_((sub_(d, b)), (mul_(d, c))));
	let temp_19_1 = (mul_((mul_((sub_(d, b)), d)), c));
	assert(eq_(temp_19_0, temp_19_1)) by {
		lemma_mul_assoc(sub_(d, b), d, c);
	}
	let temp_20_0 = (mul_((mul_(b, b)), (mod_((mul_((mod_(c, m)), b)), m))));
	let temp_20_1 = (mul_((mul_(b, b)), (mod_((sub_((mul_((mod_(c, m)), b)), (mul_((mul_((add_(d, a)), (mul_(b, b)))), m)))), m))));
	assert(eq_(temp_20_0, temp_20_1)) by {
		lemma_mul_comm(b, b);
		lemma_mod_mul_vanish(mul_(mod_(c, m), b), mul_(add_(d, a), mul_(b, b)), m);
		cong_mul_(mul_(b, b), mod_(mul_(mod_(c, m), b), m), mul_(b, b), mod_(sub_(mul_(mod_(c, m), b), mul_(mul_(add_(d, a), mul_(b, b)), m)), m));
	}
	let temp_21_0 = (mul_((mul_(c, b)), (mul_(b, d))));
	let temp_21_1 = (mul_((mul_(c, b)), (mul_(d, b))));
	assert(eq_(temp_21_0, temp_21_1)) by {
		cong_mul_(mul_(c, b), mul_(b, d), mul_(c, b), mul_(d, b));
		lemma_mul_comm(b, d);
		lemma_eq_ref(mul_(c, b));
	}
	let temp_22_0 = (mul_((mod_((mul_(b, a)), m)), (mul_(d, b))));
	let temp_22_1 = (mul_((mul_((mod_((mul_(b, a)), m)), d)), b));
	assert(eq_(temp_22_0, temp_22_1)) by {
		lemma_mul_assoc(mod_(mul_(b, a), m), d, b);
	}
	let temp_23_0 = (mul_((mul_(a, d)), (mul_(a, (mod_(b, m))))));
	let temp_23_1 = (mul_((mul_(a, d)), (mul_(a, (mod_((add_(b, (mul_((mul_((mul_(c, c)), (mul_(a, d)))), m)))), m))))));
	assert(eq_(temp_23_0, temp_23_1)) by {
		lemma_eq_ref(mul_(a, d));
		lemma_mod_mul_vanish(b, mul_(mul_(c, c), mul_(a, d)), m);
		cong_mul_(mul_(a, d), mul_(a, mod_(b, m)), mul_(a, d), mul_(a, mod_(add_(b, mul_(mul_(mul_(c, c), mul_(a, d)), m)), m)));
		cong_mul_(a, mod_(b, m), a, mod_(add_(b, mul_(mul_(mul_(c, c), mul_(a, d)), m)), m));
		lemma_eq_ref(a);
	}
	let temp_24_0 = (sub_((mul_(c, d)), (mul_(a, d))));
	let temp_24_1 = (sub_((mul_(c, d)), (mul_(d, a))));
	assert(eq_(temp_24_0, temp_24_1)) by {
		cong_sub_(mul_(c, d), mul_(a, d), mul_(c, d), mul_(d, a));
		lemma_mul_comm(a, d);
		lemma_eq_ref(mul_(c, d));
	}
	let temp_25_0 = (mul_((mul_(d, a)), (mul_(d, d))));
	let temp_25_1 = (mul_((mul_((mul_(d, a)), d)), d));
	assert(eq_(temp_25_0, temp_25_1)) by {
		lemma_mul_assoc(mul_(d, a), d, d);
	}
	let temp_26_0 = (add_((mul_(a, a)), (mul_(d, b))));
	let temp_26_1 = (add_((mul_(a, a)), (mul_(d, b))));
	assert(eq_(temp_26_0, temp_26_1)) by {
		lemma_eq_ref(temp_26_0);
	}
	let temp_27_0 = (mul_((mul_((mod_(c, m)), b)), (sub_(d, (mod_(b, m))))));
	let temp_27_1 = (mul_((mul_((mod_((sub_(c, (mul_((mul_((mul_(d, a)), (mul_(c, b)))), m)))), m)), b)), (sub_(d, (mod_(b, m))))));
	assert(eq_(temp_27_0, temp_27_1)) by {
		lemma_mod_mul_vanish(c, mul_(mul_(d, a), mul_(c, b)), m);
		cong_mul_(mul_(mod_(c, m), b), sub_(d, mod_(b, m)), mul_(mod_(sub_(c, mul_(mul_(mul_(d, a), mul_(c, b)), m)), m), b), sub_(d, mod_(b, m)));
		lemma_eq_ref(b);
		cong_mul_(mod_(c, m), b, mod_(sub_(c, mul_(mul_(mul_(d, a), mul_(c, b)), m)), m), b);
		lemma_eq_ref(sub_(d, mod_(b, m)));
	}
	let temp_28_0 = (mul_((mul_(b, (mod_(d, m)))), a));
	let temp_28_1 = (mul_((mul_((mod_(d, m)), b)), a));
	assert(eq_(temp_28_0, temp_28_1)) by {
		cong_mul_(mul_(b, mod_(d, m)), a, mul_(mod_(d, m), b), a);
		lemma_mul_comm(b, mod_(d, m));
		lemma_eq_ref(a);
	}
	let temp_29_0 = (mul_((mul_(c, b)), d));
	let temp_29_1 = (mul_(c, (mul_(b, d))));
	assert(eq_(temp_29_0, temp_29_1)) by {
		lemma_eq_sym(temp_29_1, temp_29_0);
		lemma_mul_assoc(c, b, d);
	}
	let temp_30_0 = (mul_((mul_((mod_(b, m)), (mod_(c, m)))), (mod_((mul_(d, (mod_(b, m)))), m))));
	let temp_30_1 = (mul_((mul_((mod_(b, m)), (mod_(c, m)))), (mod_((mod_((mul_(d, b)), m)), m))));
	assert(eq_(temp_30_0, temp_30_1)) by {
		lemma_mod_mul_noop(d, b, m);
		cong_mul_(mul_(mod_(b, m), mod_(c, m)), mod_(mul_(d, mod_(b, m)), m), mul_(mod_(b, m), mod_(c, m)), mod_(mod_(mul_(d, b), m), m));
		lemma_eq_sym(mod_(mod_(mul_(d, b), m), m), mod_(mul_(d, mod_(b, m)), m));
		lemma_eq_ref(mul_(mod_(b, m), mod_(c, m)));
	}
	let temp_31_0 = (mul_((sub_(a, b)), (add_(b, c))));
	let temp_31_1 = (add_((mul_((sub_(a, b)), b)), (mul_((sub_(a, b)), c))));
	assert(eq_(temp_31_0, temp_31_1)) by {
		lemma_mul_dist(sub_(a, b), b, c);
	}
	let temp_32_0 = (mul_((mod_((mul_(d, (mod_(b, m)))), m)), (sub_(b, b))));
	let temp_32_1 = (mul_((sub_(b, b)), (mod_((mul_(d, (mod_(b, m)))), m))));
	assert(eq_(temp_32_0, temp_32_1)) by {
		lemma_mul_comm(mod_(mul_(d, mod_(b, m)), m), sub_(b, b));
	}
	let temp_33_0 = (sub_((mul_(c, c)), (sub_(c, c))));
	let temp_33_1 = (sub_((mul_(c, c)), (sub_(c, c))));
	assert(eq_(temp_33_0, temp_33_1)) by {
		lemma_eq_ref(temp_33_0);
	}
	let temp_34_0 = (add_((mul_((mod_(b, m)), c)), (mul_(a, b))));
	let temp_34_1 = (add_((mul_((mod_(b, m)), c)), (mul_(b, a))));
	assert(eq_(temp_34_0, temp_34_1)) by {
		lemma_mul_comm(a, b);
		cong_add_(mul_(mod_(b, m), c), mul_(a, b), mul_(mod_(b, m), c), mul_(b, a));
		lemma_eq_ref(mul_(mod_(b, m), c));
	}
	let temp_35_0 = (mul_((mul_(a, c)), (mul_(d, a))));
	let temp_35_1 = (mul_((mul_((mul_(a, c)), d)), a));
	assert(eq_(temp_35_0, temp_35_1)) by {
		lemma_mul_assoc(mul_(a, c), d, a);
	}
	let temp_36_0 = (mul_((mul_(d, b)), (mod_((mul_(b, a)), m))));
	let temp_36_1 = (mul_(d, (mul_(b, (mod_((mul_(b, a)), m))))));
	assert(eq_(temp_36_0, temp_36_1)) by {
		lemma_mul_assoc(d, b, mod_(mul_(b, a), m));
		lemma_eq_sym(temp_36_1, temp_36_0);
	}
	let temp_37_0 = (mul_((mul_(a, b)), (add_(d, a))));
	let temp_37_1 = (mul_((mul_(a, b)), (add_(a, d))));
	assert(eq_(temp_37_0, temp_37_1)) by {
		cong_mul_(mul_(a, b), add_(d, a), mul_(a, b), add_(a, d));
		lemma_add_comm(d, a);
		lemma_eq_ref(mul_(a, b));
	}
	let temp_38_0 = (mod_((mul_((mod_((mul_((mod_(c, m)), b)), m)), (mul_(a, c)))), m));
	let temp_38_1 = (mod_((mul_((mod_((mul_(b, (mod_(c, m)))), m)), (mul_(a, c)))), m));
	assert(eq_(temp_38_0, temp_38_1)) by {
		cong_mod_(mul_(mod_(c, m), b), m, mul_(b, mod_(c, m)), m);
		cong_mul_(mod_(mul_(mod_(c, m), b), m), mul_(a, c), mod_(mul_(b, mod_(c, m)), m), mul_(a, c));
		lemma_eq_ref(mul_(a, c));
		lemma_eq_ref(m);
		lemma_mul_comm(mod_(c, m), b);
		cong_mod_(mul_(mod_(mul_(mod_(c, m), b), m), mul_(a, c)), m, mul_(mod_(mul_(b, mod_(c, m)), m), mul_(a, c)), m);
	}
	let temp_39_0 = (mul_(b, (mul_(a, b))));
	let temp_39_1 = (mul_((mul_(b, a)), b));
	assert(eq_(temp_39_0, temp_39_1)) by {
		lemma_mul_assoc(b, a, b);
	}
	let temp_40_0 = (mul_((mul_(d, d)), (mul_(a, c))));
	let temp_40_1 = (mul_((mul_(d, d)), (mul_(c, a))));
	assert(eq_(temp_40_0, temp_40_1)) by {
		cong_mul_(mul_(d, d), mul_(a, c), mul_(d, d), mul_(c, a));
		lemma_mul_comm(d, d);
		lemma_mul_comm(a, c);
	}
	let temp_41_0 = (mul_((mod_((sub_(c, c)), m)), (mod_((mul_(b, (mod_(c, m)))), m))));
	let temp_41_1 = (mul_((mod_((sub_(c, (mod_(c, m)))), m)), (mod_((mul_(b, (mod_(c, m)))), m))));
	assert(eq_(temp_41_0, temp_41_1)) by {
		cong_mul_(mod_(sub_(c, c), m), mod_(mul_(b, mod_(c, m)), m), mod_(sub_(c, mod_(c, m)), m), mod_(mul_(b, mod_(c, m)), m));
		lemma_mod_sub_noop(c, c, m);
		lemma_eq_ref(mod_(mul_(b, mod_(c, m)), m));
	}
	let temp_42_0 = (mul_((mul_(a, c)), (mul_((mod_(d, m)), d))));
	let temp_42_1 = (mul_(a, (mul_(c, (mul_((mod_(d, m)), d))))));
	assert(eq_(temp_42_0, temp_42_1)) by {
		lemma_mul_assoc(a, c, mul_(mod_(d, m), d));
		lemma_eq_sym(temp_42_1, temp_42_0);
	}
	let temp_43_0 = (mul_((mul_(d, (mod_(d, m)))), (add_(a, c))));
	let temp_43_1 = (mul_((mul_((mod_(d, m)), d)), (add_(a, c))));
	assert(eq_(temp_43_0, temp_43_1)) by {
		lemma_mul_comm(d, mod_(d, m));
		cong_mul_(mul_(d, mod_(d, m)), add_(a, c), mul_(mod_(d, m), d), add_(a, c));
		lemma_eq_ref(add_(a, c));
	}
	let temp_44_0 = (mul_((mul_(c, a)), (add_(a, b))));
	let temp_44_1 = (mul_(c, (mul_(a, (add_(a, b))))));
	assert(eq_(temp_44_0, temp_44_1)) by {
		lemma_eq_sym(temp_44_1, temp_44_0);
		lemma_mul_assoc(c, a, add_(a, b));
	}
	let temp_45_0 = (mul_((mul_(a, a)), (sub_(b, b))));
	let temp_45_1 = (mul_((mul_(a, a)), (sub_(b, b))));
	assert(eq_(temp_45_0, temp_45_1)) by {
		lemma_eq_ref(temp_45_0);
	}
	let temp_46_0 = (sub_((mul_(a, b)), (mul_(a, a))));
	let temp_46_1 = (sub_((mul_(a, b)), (mul_(a, a))));
	assert(eq_(temp_46_0, temp_46_1)) by {
		lemma_eq_ref(temp_46_0);
	}
	let temp_47_0 = (mul_(c, (mul_(c, d))));
	let temp_47_1 = (mul_((mul_(c, c)), d));
	assert(eq_(temp_47_0, temp_47_1)) by {
		lemma_mul_assoc(c, c, d);
	}
	let temp_48_0 = (mul_((mul_(d, a)), (mul_(d, d))));
	let temp_48_1 = (mul_(d, (mul_(a, (mul_(d, d))))));
	assert(eq_(temp_48_0, temp_48_1)) by {
		lemma_eq_sym(temp_48_1, temp_48_0);
		lemma_mul_assoc(d, a, mul_(d, d));
	}
	let temp_49_0 = (mul_((mul_(a, (mod_(a, m)))), (mul_((mod_(c, m)), d))));
	let temp_49_1 = (mul_(a, (mul_((mod_(a, m)), (mul_((mod_(c, m)), d))))));
	assert(eq_(temp_49_0, temp_49_1)) by {
		lemma_mul_assoc(a, mod_(a, m), mul_(mod_(c, m), d));
		lemma_eq_sym(temp_49_1, temp_49_0);
	}
	let temp_50_0 = (mul_((mul_(a, b)), (mul_(c, b))));
	let temp_50_1 = (mul_((mul_(b, a)), (mul_(c, b))));
	assert(eq_(temp_50_0, temp_50_1)) by {
		cong_mul_(mul_(a, b), mul_(c, b), mul_(b, a), mul_(c, b));
		lemma_mul_comm(a, b);
		lemma_eq_ref(mul_(c, b));
	}
	let temp_51_0 = (mul_((mul_((mod_(c, m)), c)), (mul_(b, a))));
	let temp_51_1 = (mul_((mul_((mod_((add_(c, (mul_((mod_((mul_((mod_((sub_(d, c)), m)), (sub_(d, c)))), m)), m)))), m)), c)), (mul_(b, a))));
	assert(eq_(temp_51_0, temp_51_1)) by {
		lemma_mod_mul_vanish(c, mod_(mul_(mod_(sub_(d, c), m), sub_(d, c)), m), m);
		cong_mul_(mul_(mod_(c, m), c), mul_(b, a), mul_(mod_(add_(c, mul_(mod_(mul_(mod_(sub_(d, c), m), sub_(d, c)), m), m)), m), c), mul_(b, a));
		lemma_eq_ref(c);
		cong_mul_(mod_(c, m), c, mod_(add_(c, mul_(mod_(mul_(mod_(sub_(d, c), m), sub_(d, c)), m), m)), m), c);
		lemma_eq_ref(mul_(b, a));
	}
	let temp_52_0 = (mul_((mul_(d, (mod_(c, m)))), (mod_((mul_(b, a)), m))));
	let temp_52_1 = (mul_((mod_((mul_(b, a)), m)), (mul_(d, (mod_(c, m))))));
	assert(eq_(temp_52_0, temp_52_1)) by {
		lemma_mul_comm(mul_(d, mod_(c, m)), mod_(mul_(b, a), m));
	}
	let temp_53_0 = (mul_((sub_((mod_(b, m)), (mod_(d, m)))), (mod_((mul_(b, (mod_(a, m)))), m))));
	let temp_53_1 = (mul_((mod_((mul_(b, (mod_(a, m)))), m)), (sub_((mod_(b, m)), (mod_(d, m))))));
	assert(eq_(temp_53_0, temp_53_1)) by {
		lemma_mul_comm(sub_(mod_(b, m), mod_(d, m)), mod_(mul_(b, mod_(a, m)), m));
	}
	let temp_54_0 = (sub_((mul_(d, c)), (mul_(b, b))));
	let temp_54_1 = (sub_((mul_(d, c)), (mul_(b, b))));
	assert(eq_(temp_54_0, temp_54_1)) by {
		lemma_eq_ref(temp_54_0);
	}
	let temp_55_0 = (mul_((mul_(b, c)), (mul_(a, a))));
	let temp_55_1 = (mul_((mul_(b, c)), (mul_(a, a))));
	assert(eq_(temp_55_0, temp_55_1)) by {
		lemma_eq_ref(temp_55_0);
	}
	let temp_56_0 = (mul_((sub_(d, a)), (mul_(c, d))));
	let temp_56_1 = (sub_((mul_(d, (mul_(c, d)))), (mul_(a, (mul_(c, d))))));
	assert(eq_(temp_56_0, temp_56_1)) by {
		lemma_mul_dist(mul_(c, d), d, a);
	}
	let temp_57_0 = (mul_((mul_(c, d)), (sub_(c, b))));
	let temp_57_1 = (mul_((sub_(c, b)), (mul_(c, d))));
	assert(eq_(temp_57_0, temp_57_1)) by {
		lemma_mul_comm(mul_(c, d), sub_(c, b));
	}
	let temp_58_0 = (add_((add_(a, (mod_(b, m)))), (sub_(a, a))));
	let temp_58_1 = (add_((add_(a, (mod_((add_((mul_((mul_((mod_((mul_(c, b)), m)), (mul_(c, d)))), m)), b)), m)))), (sub_(a, a))));
	assert(eq_(temp_58_0, temp_58_1)) by {
		lemma_eq_ref(a);
		cong_add_(a, mod_(b, m), a, mod_(add_(mul_(mul_(mod_(mul_(c, b), m), mul_(c, d)), m), b), m));
		cong_sub_(a, a, a, a);
		lemma_mod_mul_vanish(b, mul_(mod_(mul_(c, b), m), mul_(c, d)), m);
		cong_add_(add_(a, mod_(b, m)), sub_(a, a), add_(a, mod_(add_(mul_(mul_(mod_(mul_(c, b), m), mul_(c, d)), m), b), m)), sub_(a, a));
	}
	let temp_59_0 = (mod_((add_((mul_(a, c)), (sub_(c, c)))), m));
	let temp_59_1 = (mod_((add_((mod_((mul_(a, c)), m)), (sub_(c, c)))), m));
	assert(eq_(temp_59_0, temp_59_1)) by {
		lemma_mod_add_noop(mul_(a, c), sub_(c, c), m);
	}
	let temp_60_0 = (add_((add_(c, c)), b));
	let temp_60_1 = (add_(b, (add_(c, c))));
	assert(eq_(temp_60_0, temp_60_1)) by {
		lemma_add_comm(add_(c, c), b);
	}
	let temp_61_0 = (sub_((mul_(d, c)), (mul_(a, (mod_(d, m))))));
	let temp_61_1 = (sub_((mul_(d, c)), (mul_((mod_(d, m)), a))));
	assert(eq_(temp_61_0, temp_61_1)) by {
		lemma_eq_ref(mul_(d, c));
		lemma_mul_comm(a, mod_(d, m));
		cong_sub_(mul_(d, c), mul_(a, mod_(d, m)), mul_(d, c), mul_(mod_(d, m), a));
	}
	let temp_62_0 = (mul_((mul_(d, a)), (mul_(a, c))));
	let temp_62_1 = (mul_((mul_(d, a)), (mul_(c, a))));
	assert(eq_(temp_62_0, temp_62_1)) by {
		cong_mul_(mul_(d, a), mul_(a, c), mul_(d, a), mul_(c, a));
		lemma_mul_comm(a, c);
		lemma_eq_ref(mul_(d, a));
	}
	let temp_63_0 = (mul_((mul_(c, a)), (mul_(b, d))));
	let temp_63_1 = (mul_((mul_(c, a)), (mul_(d, b))));
	assert(eq_(temp_63_0, temp_63_1)) by {
		lemma_eq_ref(mul_(c, a));
		cong_mul_(mul_(c, a), mul_(b, d), mul_(c, a), mul_(d, b));
		lemma_mul_comm(b, d);
	}
	let temp_64_0 = (sub_((mul_(c, d)), (sub_(d, a))));
	let temp_64_1 = (sub_((mul_(d, c)), (sub_(d, a))));
	assert(eq_(temp_64_0, temp_64_1)) by {
		cong_sub_(mul_(c, d), sub_(d, a), mul_(d, c), sub_(d, a));
		lemma_mul_comm(c, d);
		lemma_eq_ref(sub_(d, a));
	}
	let temp_65_0 = (mul_((mul_(d, b)), (mul_(as_elem(54), b))));
	let temp_65_1 = (mul_((mul_(d, b)), (mul_(b, as_elem(54)))));
	assert(eq_(temp_65_0, temp_65_1)) by {
		cong_mul_(mul_(d, b), mul_(as_elem(54), b), mul_(d, b), mul_(b, as_elem(54)));
		lemma_mul_comm(as_elem(54), b);
		lemma_eq_ref(mul_(d, b));
	}
	let temp_66_0 = (mul_((mul_(d, d)), (mul_(d, d))));
	let temp_66_1 = (mul_((mul_(d, d)), (mul_(d, d))));
	assert(eq_(temp_66_0, temp_66_1)) by {
		lemma_eq_ref(temp_66_0);
	}
	let temp_67_0 = (mod_((mul_((mul_(c, c)), (mul_(b, c)))), m));
	let temp_67_1 = (mod_((mul_(c, (mul_(c, (mul_(b, c)))))), m));
	assert(eq_(temp_67_0, temp_67_1)) by {
		lemma_mul_assoc(c, c, mul_(b, c));
		cong_mod_(mul_(mul_(c, c), mul_(b, c)), m, mul_(c, mul_(c, mul_(b, c))), m);
		lemma_eq_sym(mul_(c, mul_(c, mul_(b, c))), mul_(mul_(c, c), mul_(b, c)));
		lemma_eq_ref(m);
	}
	let temp_68_0 = (mul_((add_((mod_(d, m)), c)), (mod_((add_(a, d)), m))));
	let temp_68_1 = (mul_((mod_((add_(a, d)), m)), (add_((mod_(d, m)), c))));
	assert(eq_(temp_68_0, temp_68_1)) by {
		lemma_mul_comm(add_(mod_(d, m), c), mod_(add_(a, d), m));
	}
	let temp_69_0 = (mul_((mul_(c, c)), a));
	let temp_69_1 = (mul_(c, (mul_(c, a))));
	assert(eq_(temp_69_0, temp_69_1)) by {
		lemma_eq_sym(temp_69_1, temp_69_0);
		lemma_mul_assoc(c, c, a);
	}
	let temp_70_0 = (mul_((add_(b, b)), (mod_((mul_(b, b)), m))));
	let temp_70_1 = (add_((mul_(b, (mod_((mul_(b, b)), m)))), (mul_(b, (mod_((mul_(b, b)), m))))));
	assert(eq_(temp_70_0, temp_70_1)) by {
		lemma_mul_dist(b, b, mod_(mul_(b, b), m));
	}
	let temp_71_0 = (mul_((mul_(d, c)), (mul_(c, c))));
	let temp_71_1 = (mul_((mul_(c, d)), (mul_(c, c))));
	assert(eq_(temp_71_0, temp_71_1)) by {
		cong_mul_(mul_(d, c), mul_(c, c), mul_(c, d), mul_(c, c));
		lemma_mul_comm(d, c);
		lemma_mul_comm(c, c);
	}
	let temp_72_0 = (mod_((add_((mul_(d, c)), (sub_(a, d)))), m));
	let temp_72_1 = (mod_((sub_((add_((mul_(d, c)), (sub_(a, d)))), (mul_((mul_((mul_(a, b)), (sub_(b, c)))), m)))), m));
	assert(eq_(temp_72_0, temp_72_1)) by {
		lemma_mod_mul_vanish(add_(mul_(d, c), sub_(a, d)), mul_(mul_(a, b), sub_(b, c)), m);
	}
	let temp_73_0 = (mod_((mul_((mul_(c, a)), (mul_(c, a)))), m));
	let temp_73_1 = (mod_((mul_((mul_(a, c)), (mul_(c, a)))), m));
	assert(eq_(temp_73_0, temp_73_1)) by {
		cong_mod_(mul_(mul_(c, a), mul_(c, a)), m, mul_(mul_(a, c), mul_(c, a)), m);
		lemma_mul_comm(c, a);
		lemma_mul_comm(a, c);
		lemma_eq_ref(m);
		cong_mul_(mul_(c, a), mul_(c, a), mul_(a, c), mul_(c, a));
		lemma_eq_trans(mul_(c, a), mul_(a, c), mul_(c, a));
	}
	let temp_74_0 = (mul_((mul_(d, c)), (add_(b, a))));
	let temp_74_1 = (mul_(d, (mul_(c, (add_(b, a))))));
	assert(eq_(temp_74_0, temp_74_1)) by {
		lemma_eq_sym(temp_74_1, temp_74_0);
		lemma_mul_assoc(d, c, add_(b, a));
	}
	let temp_75_0 = (mod_((add_(d, (sub_(a, (mod_(b, m)))))), m));
	let temp_75_1 = (mod_((add_((mod_(d, m)), (mod_((sub_(a, (mod_(b, m)))), m)))), m));
	assert(eq_(temp_75_0, temp_75_1)) by {
		lemma_mod_add_noop(d, sub_(a, mod_(b, m)), m);
	}
	let temp_76_0 = (mul_((mul_(d, c)), (mul_(b, c))));
	let temp_76_1 = (mul_((mul_(c, d)), (mul_(b, c))));
	assert(eq_(temp_76_0, temp_76_1)) by {
		cong_mul_(mul_(d, c), mul_(b, c), mul_(c, d), mul_(b, c));
		lemma_mul_comm(d, c);
		lemma_eq_ref(mul_(b, c));
	}
	let temp_77_0 = (mod_((mul_(d, (mul_(b, d)))), m));
	let temp_77_1 = (mod_((mul_((mul_(d, b)), d)), m));
	assert(eq_(temp_77_0, temp_77_1)) by {
		cong_mod_(mul_(d, mul_(b, d)), m, mul_(mul_(d, b), d), m);
		lemma_mul_assoc(d, b, d);
		lemma_eq_ref(m);
	}
	let temp_78_0 = (mul_((add_(b, a)), (add_(a, a))));
	let temp_78_1 = (add_((mul_((add_(b, a)), a)), (mul_((add_(b, a)), a))));
	assert(eq_(temp_78_0, temp_78_1)) by {
		lemma_mul_dist(add_(b, a), a, a);
	}
	let temp_79_0 = (add_((mul_(a, d)), (mul_(b, d))));
	let temp_79_1 = (mul_((add_(a, b)), d));
	assert(eq_(temp_79_0, temp_79_1)) by {
		lemma_eq_sym(temp_79_1, temp_79_0);
		lemma_mul_dist(a, b, d);
	}
	let temp_80_0 = (add_((mul_((mod_(a, m)), c)), (mul_(as_elem(11), b))));
	let temp_80_1 = (add_((mul_(as_elem(11), b)), (mul_((mod_(a, m)), c))));
	assert(eq_(temp_80_0, temp_80_1)) by {
		lemma_add_comm(mul_(mod_(a, m), c), mul_(as_elem(11), b));
	}
	let temp_81_0 = (mul_((mul_(a, a)), (mul_(c, d))));
	let temp_81_1 = (mul_((mul_((mul_(a, a)), c)), d));
	assert(eq_(temp_81_0, temp_81_1)) by {
		lemma_mul_assoc(mul_(a, a), c, d);
	}
	let temp_82_0 = (mod_((add_((add_(c, as_elem(59))), (mul_(b, c)))), m));
	let temp_82_1 = (mod_((add_((add_(c, as_elem(59))), (mod_((mul_(b, c)), m)))), m));
	assert(eq_(temp_82_0, temp_82_1)) by {
		lemma_mod_add_noop(add_(c, as_elem(59)), mul_(b, c), m);
	}
	let temp_83_0 = (mul_((mod_((mul_(d, b)), m)), (mul_(c, d))));
	let temp_83_1 = (mul_((mul_(c, d)), (mod_((mul_(d, b)), m))));
	assert(eq_(temp_83_0, temp_83_1)) by {
		lemma_mul_comm(mod_(mul_(d, b), m), mul_(c, d));
	}
	let temp_84_0 = (mod_((mul_((mul_(a, d)), (mul_(c, d)))), m));
	let temp_84_1 = (mod_((mul_((mul_((mul_(a, d)), c)), d)), m));
	assert(eq_(temp_84_0, temp_84_1)) by {
		lemma_mul_assoc(mul_(a, d), c, d);
		cong_mod_(mul_(mul_(a, d), mul_(c, d)), m, mul_(mul_(mul_(a, d), c), d), m);
		lemma_eq_ref(m);
	}
	let temp_85_0 = (mul_((mul_(d, b)), (mul_(a, a))));
	let temp_85_1 = (mul_(d, (mul_(b, (mul_(a, a))))));
	assert(eq_(temp_85_0, temp_85_1)) by {
		lemma_eq_sym(temp_85_1, temp_85_0);
		lemma_mul_assoc(d, b, mul_(a, a));
	}
	let temp_86_0 = (sub_((mod_((mul_(a, c)), m)), (mul_(b, b))));
	let temp_86_1 = (sub_((mod_((mul_(a, c)), m)), (mul_(b, b))));
	assert(eq_(temp_86_0, temp_86_1)) by {
		lemma_eq_ref(temp_86_0);
	}
	let temp_87_0 = (mul_((mul_(c, c)), (add_(a, a))));
	let temp_87_1 = (mul_((add_(a, a)), (mul_(c, c))));
	assert(eq_(temp_87_0, temp_87_1)) by {
		lemma_mul_comm(mul_(c, c), add_(a, a));
	}
	let temp_88_0 = (mul_((mod_((mul_(c, c)), m)), (mul_(d, c))));
	let temp_88_1 = (mul_((mod_((add_((mul_(c, c)), (mul_((mul_((mul_(b, d)), (add_(b, b)))), m)))), m)), (mul_(d, c))));
	assert(eq_(temp_88_0, temp_88_1)) by {
		lemma_mod_mul_vanish(mul_(c, c), mul_(mul_(b, d), add_(b, b)), m);
		cong_mul_(mod_(mul_(c, c), m), mul_(d, c), mod_(add_(mul_(c, c), mul_(mul_(mul_(b, d), add_(b, b)), m)), m), mul_(d, c));
		lemma_eq_ref(mul_(d, c));
	}
	let temp_89_0 = (mul_((mod_((mul_(b, d)), m)), (mul_(a, c))));
	let temp_89_1 = (mul_((mul_(a, c)), (mod_((mul_(b, d)), m))));
	assert(eq_(temp_89_0, temp_89_1)) by {
		lemma_mul_comm(mod_(mul_(b, d), m), mul_(a, c));
	}
	let temp_90_0 = (mod_((mul_((mul_(c, a)), (mul_(c, c)))), m));
	let temp_90_1 = (mod_((mul_((mul_((mul_(c, a)), c)), c)), m));
	assert(eq_(temp_90_0, temp_90_1)) by {
		lemma_mul_assoc(mul_(c, a), c, c);
		cong_mod_(mul_(mul_(c, a), mul_(c, c)), m, mul_(mul_(mul_(c, a), c), c), m);
		lemma_eq_ref(m);
	}
	let temp_91_0 = (sub_((mul_(d, c)), (mul_(as_elem(50), b))));
	let temp_91_1 = (sub_((mul_(c, d)), (mul_(as_elem(50), b))));
	assert(eq_(temp_91_0, temp_91_1)) by {
		lemma_mul_comm(d, c);
		cong_sub_(mul_(d, c), mul_(as_elem(50), b), mul_(c, d), mul_(as_elem(50), b));
		lemma_eq_ref(mul_(as_elem(50), b));
	}
	let temp_92_0 = (mul_((mul_(b, c)), (mod_((mul_(b, d)), m))));
	let temp_92_1 = (mul_(b, (mul_(c, (mod_((mul_(b, d)), m))))));
	assert(eq_(temp_92_0, temp_92_1)) by {
		lemma_mul_assoc(b, c, mod_(mul_(b, d), m));
		lemma_eq_sym(temp_92_1, temp_92_0);
	}
	let temp_93_0 = (mul_((mul_(c, a)), (mul_(a, c))));
	let temp_93_1 = (mul_((mul_((mul_(c, a)), a)), c));
	assert(eq_(temp_93_0, temp_93_1)) by {
		lemma_mul_assoc(mul_(c, a), a, c);
	}
	let temp_94_0 = (mul_((add_(d, d)), (mul_(c, b))));
	let temp_94_1 = (add_((mul_(d, (mul_(c, b)))), (mul_(d, (mul_(c, b))))));
	assert(eq_(temp_94_0, temp_94_1)) by {
		lemma_mul_dist(d, d, mul_(c, b));
	}
	let temp_95_0 = (sub_((sub_(d, d)), (mul_(as_elem(48), b))));
	let temp_95_1 = (sub_((sub_(d, d)), (mul_(b, as_elem(48)))));
	assert(eq_(temp_95_0, temp_95_1)) by {
		cong_sub_(sub_(d, d), mul_(as_elem(48), b), sub_(d, d), mul_(b, as_elem(48)));
		lemma_mul_comm(as_elem(48), b);
		lemma_eq_ref(sub_(d, d));
	}
	let temp_96_0 = (add_((mul_(a, b)), (mul_(d, b))));
	let temp_96_1 = (mul_((add_(a, d)), b));
	assert(eq_(temp_96_0, temp_96_1)) by {
		lemma_eq_sym(temp_96_1, temp_96_0);
		lemma_mul_dist(a, d, b);
	}
	let temp_97_0 = (mul_((mul_(b, b)), (mul_(c, d))));
	let temp_97_1 = (mul_((mul_(c, d)), (mul_(b, b))));
	assert(eq_(temp_97_0, temp_97_1)) by {
		lemma_mul_comm(mul_(b, b), mul_(c, d));
	}
	let temp_98_0 = (add_((mul_(b, (mod_(c, m)))), (mul_(c, d))));
	let temp_98_1 = (add_((mul_(c, d)), (mul_(b, (mod_(c, m))))));
	assert(eq_(temp_98_0, temp_98_1)) by {
		lemma_add_comm(mul_(b, mod_(c, m)), mul_(c, d));
	}
	let temp_99_0 = (sub_((mul_(d, d)), (mul_(a, c))));
	let temp_99_1 = (sub_((mul_(d, d)), (mul_(c, a))));
	assert(eq_(temp_99_0, temp_99_1)) by {
		cong_sub_(mul_(d, d), mul_(a, c), mul_(d, d), mul_(c, a));
		lemma_mul_comm(a, c);
		lemma_eq_ref(mul_(d, d));
	}
	let temp_100_0 = (mul_((mul_(b, (mod_(c, m)))), (mul_(b, a))));
	let temp_100_1 = (mul_((mul_((mul_(b, (mod_(c, m)))), b)), a));
	assert(eq_(temp_100_0, temp_100_1)) by {
		lemma_mul_assoc(mul_(b, mod_(c, m)), b, a);
	}
	let temp_101_0 = (sub_((mul_(d, b)), (add_(b, d))));
	let temp_101_1 = (sub_((mul_(b, d)), (add_(b, d))));
	assert(eq_(temp_101_0, temp_101_1)) by {
		cong_sub_(mul_(d, b), add_(b, d), mul_(b, d), add_(b, d));
		lemma_mul_comm(d, b);
		lemma_eq_ref(add_(b, d));
	}
	let temp_102_0 = (mul_((mul_(c, as_elem(14))), (mul_(c, a))));
	let temp_102_1 = (mul_((mul_(as_elem(14), c)), (mul_(c, a))));
	assert(eq_(temp_102_0, temp_102_1)) by {
		cong_mul_(mul_(c, as_elem(14)), mul_(c, a), mul_(as_elem(14), c), mul_(c, a));
		lemma_mul_comm(c, as_elem(14));
		lemma_eq_ref(mul_(c, a));
	}
	let temp_103_0 = (add_((mod_((mul_(b, a)), m)), (mod_((mul_(c, c)), m))));
	let temp_103_1 = (add_((mod_((mul_(b, a)), m)), (mod_((sub_((mul_(c, c)), (mul_((sub_((mul_(c, c)), (mul_(a, a)))), m)))), m))));
	assert(eq_(temp_103_0, temp_103_1)) by {
		lemma_mod_mul_vanish(mul_(c, c), sub_(mul_(c, c), mul_(a, a)), m);
		cong_add_(mod_(mul_(b, a), m), mod_(mul_(c, c), m), mod_(mul_(b, a), m), mod_(sub_(mul_(c, c), mul_(sub_(mul_(c, c), mul_(a, a)), m)), m));
		lemma_eq_ref(mod_(mul_(b, a), m));
	}
	let temp_104_0 = (mul_((mod_((mul_(d, a)), m)), (add_(b, a))));
	let temp_104_1 = (mul_((mod_((add_((mul_(d, a)), (mul_((add_((mul_(b, d)), (mul_(as_elem(6), a)))), m)))), m)), (add_(b, a))));
	assert(eq_(temp_104_0, temp_104_1)) by {
		lemma_mod_mul_vanish(mul_(d, a), add_(mul_(b, d), mul_(as_elem(6), a)), m);
		cong_mul_(mod_(mul_(d, a), m), add_(b, a), mod_(add_(mul_(d, a), mul_(add_(mul_(b, d), mul_(as_elem(6), a)), m)), m), add_(b, a));
		lemma_eq_ref(add_(b, a));
	}
	let temp_105_0 = (mod_((mul_((mul_(c, b)), (mul_(c, d)))), m));
	let temp_105_1 = (mod_((mul_((mul_((mul_(c, b)), c)), d)), m));
	assert(eq_(temp_105_0, temp_105_1)) by {
		lemma_mul_assoc(mul_(c, b), c, d);
		cong_mod_(mul_(mul_(c, b), mul_(c, d)), m, mul_(mul_(mul_(c, b), c), d), m);
		lemma_eq_ref(m);
	}
	let temp_106_0 = (mul_((mul_((mod_(d, m)), c)), (mul_(a, as_elem(44)))));
	let temp_106_1 = (mul_((mul_((mod_((add_((mul_((mul_((mul_(d, c)), (mul_(a, c)))), m)), d)), m)), c)), (mul_(a, as_elem(44)))));
	assert(eq_(temp_106_0, temp_106_1)) by {
		cong_mul_(mod_(d, m), c, mod_(add_(mul_(mul_(mul_(d, c), mul_(a, c)), m), d), m), c);
		lemma_eq_ref(mul_(a, as_elem(44)));
		lemma_eq_ref(c);
		lemma_mod_mul_vanish(d, mul_(mul_(d, c), mul_(a, c)), m);
		cong_mul_(mul_(mod_(d, m), c), mul_(a, as_elem(44)), mul_(mod_(add_(mul_(mul_(mul_(d, c), mul_(a, c)), m), d), m), c), mul_(a, as_elem(44)));
	}
	let temp_107_0 = (mul_((mul_(d, c)), (mul_((mod_(a, m)), c))));
	let temp_107_1 = (mul_((mul_((mod_(a, m)), c)), (mul_(d, c))));
	assert(eq_(temp_107_0, temp_107_1)) by {
		lemma_mul_comm(mul_(d, c), mul_(mod_(a, m), c));
	}
	let temp_108_0 = (mul_((mul_(d, a)), (mul_(d, (mod_(d, m))))));
	let temp_108_1 = (mul_((mul_((mul_(d, a)), d)), (mod_(d, m))));
	assert(eq_(temp_108_0, temp_108_1)) by {
		lemma_mul_assoc(mul_(d, a), d, mod_(d, m));
	}
	let temp_109_0 = (mul_((mod_((mul_(d, c)), m)), (mul_(a, (mod_(a, m))))));
	let temp_109_1 = (mul_((mul_((mod_((mul_(d, c)), m)), a)), (mod_(a, m))));
	assert(eq_(temp_109_0, temp_109_1)) by {
		lemma_mul_assoc(mod_(mul_(d, c), m), a, mod_(a, m));
	}
	let temp_110_0 = (mul_((mul_(a, b)), (mul_(d, d))));
	let temp_110_1 = (mul_((mul_(b, a)), (mul_(d, d))));
	assert(eq_(temp_110_0, temp_110_1)) by {
		cong_mul_(mul_(a, b), mul_(d, d), mul_(b, a), mul_(d, d));
		lemma_mul_comm(a, b);
		lemma_mul_comm(d, d);
	}
	let temp_111_0 = (mul_((mul_(d, b)), (mul_(b, c))));
	let temp_111_1 = (mul_((mul_(b, d)), (mul_(b, c))));
	assert(eq_(temp_111_0, temp_111_1)) by {
		cong_mul_(mul_(d, b), mul_(b, c), mul_(b, d), mul_(b, c));
		lemma_mul_comm(d, b);
		lemma_eq_ref(mul_(b, c));
	}
	let temp_112_0 = (mul_((mul_((mod_(d, m)), (mod_(b, m)))), (mul_(c, c))));
	let temp_112_1 = (mul_((mul_((mul_((mod_(d, m)), (mod_(b, m)))), c)), c));
	assert(eq_(temp_112_0, temp_112_1)) by {
		lemma_mul_assoc(mul_(mod_(d, m), mod_(b, m)), c, c);
	}
	let temp_113_0 = (mul_((mul_(b, (mod_(a, m)))), (mul_(c, b))));
	let temp_113_1 = (mul_((mul_(b, (mod_((sub_(a, (mul_((mul_((mod_((mul_(a, a)), m)), (mul_(b, c)))), m)))), m)))), (mul_(c, b))));
	assert(eq_(temp_113_0, temp_113_1)) by {
		lemma_mod_mul_vanish(a, mul_(mod_(mul_(a, a), m), mul_(b, c)), m);
		cong_mul_(mul_(b, mod_(a, m)), mul_(c, b), mul_(b, mod_(sub_(a, mul_(mul_(mod_(mul_(a, a), m), mul_(b, c)), m)), m)), mul_(c, b));
		lemma_eq_ref(b);
		lemma_eq_ref(mul_(c, b));
		cong_mul_(b, mod_(a, m), b, mod_(sub_(a, mul_(mul_(mod_(mul_(a, a), m), mul_(b, c)), m)), m));
	}
	let temp_114_0 = (mul_((mul_(b, d)), (mul_(b, (mod_(c, m))))));
	let temp_114_1 = (mul_((mul_(b, d)), (mul_((mod_(c, m)), b))));
	assert(eq_(temp_114_0, temp_114_1)) by {
		lemma_eq_ref(mul_(b, d));
		lemma_mul_comm(b, mod_(c, m));
		cong_mul_(mul_(b, d), mul_(b, mod_(c, m)), mul_(b, d), mul_(mod_(c, m), b));
	}
	let temp_115_0 = (sub_((mod_((add_(a, a)), m)), (mul_(d, b))));
	let temp_115_1 = (sub_((mod_((add_(a, (mod_(a, m)))), m)), (mul_(d, b))));
	assert(eq_(temp_115_0, temp_115_1)) by {
		lemma_mod_add_noop(a, a, m);
		cong_sub_(mod_(add_(a, a), m), mul_(d, b), mod_(add_(a, mod_(a, m)), m), mul_(d, b));
		lemma_eq_ref(mul_(d, b));
	}
	let temp_116_0 = (mul_((mul_((mod_(a, m)), a)), (mod_((mul_(b, b)), m))));
	let temp_116_1 = (mul_((mul_((mod_(a, m)), a)), (mod_((mul_(b, b)), m))));
	assert(eq_(temp_116_0, temp_116_1)) by {
		lemma_eq_ref(temp_116_0);
	}
	let temp_117_0 = (mul_((mul_(c, b)), (mul_(b, (mod_(c, m))))));
	let temp_117_1 = (mul_((mul_(b, c)), (mul_(b, (mod_(c, m))))));
	assert(eq_(temp_117_0, temp_117_1)) by {
		cong_mul_(mul_(c, b), mul_(b, mod_(c, m)), mul_(b, c), mul_(b, mod_(c, m)));
		lemma_mul_comm(c, b);
		lemma_eq_ref(mul_(b, mod_(c, m)));
	}
	let temp_118_0 = (mul_((add_((mod_(a, m)), (mod_(a, m)))), (mul_(a, a))));
	let temp_118_1 = (mul_((add_((mod_(a, m)), (mod_(a, m)))), (mul_(a, a))));
	assert(eq_(temp_118_0, temp_118_1)) by {
		lemma_eq_ref(temp_118_0);
	}
	let temp_119_0 = (sub_((mod_((mul_(d, a)), m)), (mul_((mod_(b, m)), d))));
	let temp_119_1 = (sub_((mod_((add_((mul_((mod_((mul_((mul_(d, b)), (mul_(d, d)))), m)), m)), (mul_(d, a)))), m)), (mul_((mod_(b, m)), d))));
	assert(eq_(temp_119_0, temp_119_1)) by {
		lemma_mod_mul_vanish(mul_(d, a), mod_(mul_(mul_(d, b), mul_(d, d)), m), m);
		cong_sub_(mod_(mul_(d, a), m), mul_(mod_(b, m), d), mod_(add_(mul_(mod_(mul_(mul_(d, b), mul_(d, d)), m), m), mul_(d, a)), m), mul_(mod_(b, m), d));
		lemma_eq_ref(mul_(mod_(b, m), d));
	}
	let temp_120_0 = (sub_((mul_(c, (mod_(a, m)))), (mul_(a, d))));
	let temp_120_1 = (sub_((mul_(c, (mod_((add_((mul_((mul_((add_(a, d)), (mul_(d, c)))), m)), a)), m)))), (mul_(a, d))));
	assert(eq_(temp_120_0, temp_120_1)) by {
		lemma_mod_mul_vanish(a, mul_(add_(a, d), mul_(d, c)), m);
		cong_sub_(mul_(c, mod_(a, m)), mul_(a, d), mul_(c, mod_(add_(mul_(mul_(add_(a, d), mul_(d, c)), m), a), m)), mul_(a, d));
		lemma_eq_ref(c);
		cong_mul_(c, mod_(a, m), c, mod_(add_(mul_(mul_(add_(a, d), mul_(d, c)), m), a), m));
		lemma_eq_ref(mul_(a, d));
	}
	let temp_121_0 = (mul_((mul_(d, a)), (add_(a, a))));
	let temp_121_1 = (mul_((add_(a, a)), (mul_(d, a))));
	assert(eq_(temp_121_0, temp_121_1)) by {
		lemma_mul_comm(mul_(d, a), add_(a, a));
	}
	let temp_122_0 = (mod_((add_((mul_(b, c)), (mul_(b, c)))), m));
	let temp_122_1 = (mod_((mul_((add_(b, b)), c)), m));
	assert(eq_(temp_122_0, temp_122_1)) by {
		cong_mod_(add_(mul_(b, c), mul_(b, c)), m, mul_(add_(b, b), c), m);
		lemma_mul_dist(b, b, c);
		lemma_eq_sym(mul_(add_(b, b), c), add_(mul_(b, c), mul_(b, c)));
		lemma_eq_ref(m);
	}
	let temp_123_0 = (mul_((mul_((mod_(c, m)), d)), (mul_(d, (mod_(b, m))))));
	let temp_123_1 = (mul_((mul_(d, (mod_(c, m)))), (mul_(d, (mod_(b, m))))));
	assert(eq_(temp_123_0, temp_123_1)) by {
		lemma_mul_comm(mod_(c, m), d);
		cong_mul_(mul_(mod_(c, m), d), mul_(d, mod_(b, m)), mul_(d, mod_(c, m)), mul_(d, mod_(b, m)));
		lemma_eq_ref(mul_(d, mod_(b, m)));
	}
	let temp_124_0 = (mul_((mul_(d, c)), (mul_(b, c))));
	let temp_124_1 = (mul_((mul_((mul_(d, c)), b)), c));
	assert(eq_(temp_124_0, temp_124_1)) by {
		lemma_mul_assoc(mul_(d, c), b, c);
	}
	let temp_125_0 = (mul_((mul_(d, d)), (add_((mod_(c, m)), c))));
	let temp_125_1 = (mul_(d, (mul_(d, (add_((mod_(c, m)), c))))));
	assert(eq_(temp_125_0, temp_125_1)) by {
		lemma_eq_sym(temp_125_1, temp_125_0);
		lemma_mul_assoc(d, d, add_(mod_(c, m), c));
	}
	let temp_126_0 = (mul_((mul_(d, a)), (mul_(a, b))));
	let temp_126_1 = (mul_((mul_(a, b)), (mul_(d, a))));
	assert(eq_(temp_126_0, temp_126_1)) by {
		lemma_mul_comm(mul_(d, a), mul_(a, b));
	}
	let temp_127_0 = (mul_((mul_(c, b)), (mod_((mul_((mod_(d, m)), (mod_(d, m)))), m))));
	let temp_127_1 = (mul_((mul_(c, b)), (mod_((mod_((mul_((mod_(d, m)), d)), m)), m))));
	assert(eq_(temp_127_0, temp_127_1)) by {
		lemma_mod_mul_noop(mod_(d, m), d, m);
		cong_mul_(mul_(c, b), mod_(mul_(mod_(d, m), mod_(d, m)), m), mul_(c, b), mod_(mod_(mul_(mod_(d, m), d), m), m));
		lemma_eq_sym(mod_(mod_(mul_(mod_(d, m), d), m), m), mod_(mul_(mod_(d, m), mod_(d, m)), m));
		lemma_eq_ref(mul_(c, b));
	}
	let temp_128_0 = (mul_((mul_(d, c)), (mul_(b, b))));
	let temp_128_1 = (mul_((mul_((mul_(d, c)), b)), b));
	assert(eq_(temp_128_0, temp_128_1)) by {
		lemma_mul_assoc(mul_(d, c), b, b);
	}
	let temp_129_0 = (mul_((mul_(c, b)), (mul_(c, c))));
	let temp_129_1 = (mul_(c, (mul_(b, (mul_(c, c))))));
	assert(eq_(temp_129_0, temp_129_1)) by {
		lemma_eq_sym(temp_129_1, temp_129_0);
		lemma_mul_assoc(c, b, mul_(c, c));
	}
	let temp_130_0 = (mul_((mul_(c, (mod_(d, m)))), (add_(b, c))));
	let temp_130_1 = (mul_((mul_(c, (mod_((add_((mul_((mod_((mul_((mul_(a, d)), (mul_(d, d)))), m)), m)), d)), m)))), (add_(b, c))));
	assert(eq_(temp_130_0, temp_130_1)) by {
		lemma_mod_mul_vanish(d, mod_(mul_(mul_(a, d), mul_(d, d)), m), m);
		cong_mul_(mul_(c, mod_(d, m)), add_(b, c), mul_(c, mod_(add_(mul_(mod_(mul_(mul_(a, d), mul_(d, d)), m), m), d), m)), add_(b, c));
		lemma_eq_ref(c);
		cong_mul_(c, mod_(d, m), c, mod_(add_(mul_(mod_(mul_(mul_(a, d), mul_(d, d)), m), m), d), m));
		lemma_eq_ref(add_(b, c));
	}
	let temp_131_0 = (mul_((mul_(c, a)), (mod_((mul_(c, c)), m))));
	let temp_131_1 = (mul_((mul_(c, a)), (mod_((mul_(c, c)), m))));
	assert(eq_(temp_131_0, temp_131_1)) by {
		lemma_eq_ref(temp_131_0);
	}
	let temp_132_0 = (mul_((add_(c, d)), (sub_(a, c))));
	let temp_132_1 = (add_((mul_(c, (sub_(a, c)))), (mul_(d, (sub_(a, c))))));
	assert(eq_(temp_132_0, temp_132_1)) by {
		lemma_mul_dist(c, d, sub_(a, c));
	}

}

} // verus!