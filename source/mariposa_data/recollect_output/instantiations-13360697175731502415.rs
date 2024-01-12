use builtin_macros::*;
// use builtin::*;
mod nl_basics;
use crate::nl_basics::*;
verus! {

pub proof fn free_0(a: Elem, b: Elem, c: Elem, d: Elem, m: Elem)
{
	let temp_0_0 = (mul_((mul_((mod_(c, m)), b)), (mul_(c, c))));
	let temp_0_1 = (mul_((mul_(c, c)), (mul_((mod_(c, m)), b))));
	assert(eq_(temp_0_0, temp_0_1)) by {
		lemma_mul_comm(mul_(mod_(c, m), b), mul_(c, c));
	}
	let temp_1_0 = (mul_((mul_(b, (mod_(d, m)))), (mul_(as_elem(37), b))));
	let temp_1_1 = (mul_((mul_(b, (mod_((sub_(d, (mul_((mul_((mul_(a, c)), (mul_(b, b)))), m)))), m)))), (mul_(as_elem(37), b))));
	assert(eq_(temp_1_0, temp_1_1)) by {
		cong_mul_(mul_(b, mod_(d, m)), mul_(as_elem(37), b), mul_(b, mod_(sub_(d, mul_(mul_(mul_(a, c), mul_(b, b)), m)), m)), mul_(as_elem(37), b));
		lemma_mod_mul_vanish(d, mul_(mul_(a, c), mul_(b, b)), m);
		lemma_eq_ref(b);
		cong_mul_(b, mod_(d, m), b, mod_(sub_(d, mul_(mul_(mul_(a, c), mul_(b, b)), m)), m));
		lemma_eq_ref(mul_(as_elem(37), b));
	}
	let temp_2_0 = (sub_((mul_(c, (mod_(c, m)))), (add_((mod_(d, m)), a))));
	let temp_2_1 = (sub_((mul_(c, (mod_(c, m)))), (add_((mod_((sub_(d, (mul_((mul_((mul_((mod_(d, m)), a)), (mul_(a, b)))), m)))), m)), a))));
	assert(eq_(temp_2_0, temp_2_1)) by {
		cong_add_(mod_(d, m), a, mod_(sub_(d, mul_(mul_(mul_(mod_(d, m), a), mul_(a, b)), m)), m), a);
		lemma_eq_ref(a);
		lemma_eq_ref(mul_(c, mod_(c, m)));
		lemma_mod_mul_vanish(d, mul_(mul_(mod_(d, m), a), mul_(a, b)), m);
		cong_sub_(mul_(c, mod_(c, m)), add_(mod_(d, m), a), mul_(c, mod_(c, m)), add_(mod_(sub_(d, mul_(mul_(mul_(mod_(d, m), a), mul_(a, b)), m)), m), a));
	}
	let temp_3_0 = (mul_((mul_(c, c)), (mul_((mod_(a, m)), c))));
	let temp_3_1 = (mul_((mul_((mul_(c, c)), (mod_(a, m)))), c));
	assert(eq_(temp_3_0, temp_3_1)) by {
		lemma_mul_assoc(mul_(c, c), mod_(a, m), c);
	}
	let temp_4_0 = (mod_((mul_((mul_(d, c)), (mul_(a, b)))), m));
	let temp_4_1 = (mod_((sub_((mul_((mul_(d, c)), (mul_(a, b)))), (mul_((mul_((mul_(c, d)), (mul_(b, a)))), m)))), m));
	assert(eq_(temp_4_0, temp_4_1)) by {
		lemma_mod_mul_vanish(mul_(mul_(d, c), mul_(a, b)), mul_(mul_(c, d), mul_(b, a)), m);
	}
	let temp_5_0 = (mul_((mul_(c, b)), (mul_(a, d))));
	let temp_5_1 = (mul_((mul_(a, d)), (mul_(c, b))));
	assert(eq_(temp_5_0, temp_5_1)) by {
		lemma_mul_comm(mul_(c, b), mul_(a, d));
	}
	let temp_6_0 = (mul_((mod_((mul_(b, d)), m)), (mul_(c, a))));
	let temp_6_1 = (mul_((mod_((sub_((mul_(b, d)), (mul_((mul_((add_(d, c)), (mul_(c, a)))), m)))), m)), (mul_(c, a))));
	assert(eq_(temp_6_0, temp_6_1)) by {
		lemma_mod_mul_vanish(mul_(b, d), mul_(add_(d, c), mul_(c, a)), m);
		cong_mul_(mod_(mul_(b, d), m), mul_(c, a), mod_(sub_(mul_(b, d), mul_(mul_(add_(d, c), mul_(c, a)), m)), m), mul_(c, a));
		lemma_eq_ref(mul_(c, a));
	}
	let temp_7_0 = (mul_((mul_(c, b)), (mul_(d, a))));
	let temp_7_1 = (mul_((mul_(d, a)), (mul_(c, b))));
	assert(eq_(temp_7_0, temp_7_1)) by {
		lemma_mul_comm(mul_(c, b), mul_(d, a));
	}
	let temp_8_0 = (mul_((mul_(c, a)), (mod_((mul_(a, b)), m))));
	let temp_8_1 = (mul_(c, (mul_(a, (mod_((mul_(a, b)), m))))));
	assert(eq_(temp_8_0, temp_8_1)) by {
		lemma_mul_assoc(c, a, mod_(mul_(a, b), m));
		lemma_eq_sym(temp_8_1, temp_8_0);
	}
	let temp_9_0 = (mul_((mul_(d, b)), (mul_(b, a))));
	let temp_9_1 = (mul_((mul_((mul_(d, b)), b)), a));
	assert(eq_(temp_9_0, temp_9_1)) by {
		lemma_mul_assoc(mul_(d, b), b, a);
	}
	let temp_10_0 = (mul_((mul_((mod_(b, m)), a)), (mul_(c, d))));
	let temp_10_1 = (mul_((mul_((mul_((mod_(b, m)), a)), c)), d));
	assert(eq_(temp_10_0, temp_10_1)) by {
		lemma_mul_assoc(mul_(mod_(b, m), a), c, d);
	}
	let temp_11_0 = (mul_((mul_(a, d)), (mul_(c, a))));
	let temp_11_1 = (mul_(a, (mul_(d, (mul_(c, a))))));
	assert(eq_(temp_11_0, temp_11_1)) by {
		lemma_eq_sym(temp_11_1, temp_11_0);
		lemma_mul_assoc(a, d, mul_(c, a));
	}
	let temp_12_0 = (sub_((mod_((mul_(d, d)), m)), a));
	let temp_12_1 = (sub_((mod_((mul_(d, d)), m)), a));
	assert(eq_(temp_12_0, temp_12_1)) by {
		lemma_eq_ref(temp_12_0);
	}
	let temp_13_0 = (mul_((mul_(d, (mod_(c, m)))), (add_(a, d))));
	let temp_13_1 = (mul_((mul_(d, (mod_((sub_(c, (mul_((add_((mul_(a, d)), (mul_(a, (mod_(c, m)))))), m)))), m)))), (add_(a, d))));
	assert(eq_(temp_13_0, temp_13_1)) by {
		cong_mul_(d, mod_(c, m), d, mod_(sub_(c, mul_(add_(mul_(a, d), mul_(a, mod_(c, m))), m)), m));
		lemma_eq_ref(add_(a, d));
		lemma_eq_ref(d);
		lemma_mod_mul_vanish(c, add_(mul_(a, d), mul_(a, mod_(c, m))), m);
		cong_mul_(mul_(d, mod_(c, m)), add_(a, d), mul_(d, mod_(sub_(c, mul_(add_(mul_(a, d), mul_(a, mod_(c, m))), m)), m)), add_(a, d));
	}
	let temp_14_0 = (mul_((mul_((mod_(c, m)), a)), (mul_(d, d))));
	let temp_14_1 = (mul_((mul_((mul_((mod_(c, m)), a)), d)), d));
	assert(eq_(temp_14_0, temp_14_1)) by {
		lemma_mul_assoc(mul_(mod_(c, m), a), d, d);
	}
	let temp_15_0 = (mul_((mul_(c, c)), (sub_(d, d))));
	let temp_15_1 = (mul_(c, (mul_(c, (sub_(d, d))))));
	assert(eq_(temp_15_0, temp_15_1)) by {
		lemma_eq_sym(temp_15_1, temp_15_0);
		lemma_mul_assoc(c, c, sub_(d, d));
	}
	let temp_16_0 = (mul_((mod_((mul_(d, c)), m)), (add_(b, b))));
	let temp_16_1 = (mul_((mod_((sub_((mul_(d, c)), (mul_((mul_((mul_(d, d)), (mul_(a, a)))), m)))), m)), (add_(b, b))));
	assert(eq_(temp_16_0, temp_16_1)) by {
		lemma_add_comm(b, b);
		lemma_mod_mul_vanish(mul_(d, c), mul_(mul_(d, d), mul_(a, a)), m);
		cong_mul_(mod_(mul_(d, c), m), add_(b, b), mod_(sub_(mul_(d, c), mul_(mul_(mul_(d, d), mul_(a, a)), m)), m), add_(b, b));
	}
	let temp_17_0 = (mod_((mul_((mod_((mul_(a, d)), m)), (mul_(a, d)))), m));
	let temp_17_1 = (mod_((mul_((mod_((add_((mul_(a, d)), (mul_((mul_((add_(c, (mod_(a, m)))), (mul_(b, a)))), m)))), m)), (mul_(a, d)))), m));
	assert(eq_(temp_17_0, temp_17_1)) by {
		lemma_mod_mul_vanish(mul_(a, d), mul_(add_(c, mod_(a, m)), mul_(b, a)), m);
		cong_mod_(mul_(mod_(mul_(a, d), m), mul_(a, d)), m, mul_(mod_(add_(mul_(a, d), mul_(mul_(add_(c, mod_(a, m)), mul_(b, a)), m)), m), mul_(a, d)), m);
		lemma_eq_ref(mul_(a, d));
		lemma_eq_ref(m);
		cong_mul_(mod_(mul_(a, d), m), mul_(a, d), mod_(add_(mul_(a, d), mul_(mul_(add_(c, mod_(a, m)), mul_(b, a)), m)), m), mul_(a, d));
	}
	let temp_18_0 = (mul_((sub_(c, a)), (mod_((sub_((mod_(b, m)), b)), m))));
	let temp_18_1 = (mul_((mod_((sub_((mod_(b, m)), b)), m)), (sub_(c, a))));
	assert(eq_(temp_18_0, temp_18_1)) by {
		lemma_mul_comm(sub_(c, a), mod_(sub_(mod_(b, m), b), m));
	}
	let temp_19_0 = (mul_((mul_((mod_(a, m)), c)), (add_(d, d))));
	let temp_19_1 = (mul_((mul_(c, (mod_(a, m)))), (add_(d, d))));
	assert(eq_(temp_19_0, temp_19_1)) by {
		lemma_mul_comm(mod_(a, m), c);
		lemma_add_comm(d, d);
		cong_mul_(mul_(mod_(a, m), c), add_(d, d), mul_(c, mod_(a, m)), add_(d, d));
	}
	let temp_20_0 = (mul_((add_((mod_(as_elem(17), m)), b)), (mul_(d, c))));
	let temp_20_1 = (mul_((add_(b, (mod_(as_elem(17), m)))), (mul_(d, c))));
	assert(eq_(temp_20_0, temp_20_1)) by {
		lemma_add_comm(mod_(as_elem(17), m), b);
		cong_mul_(add_(mod_(as_elem(17), m), b), mul_(d, c), add_(b, mod_(as_elem(17), m)), mul_(d, c));
		lemma_eq_ref(mul_(d, c));
	}
	let temp_21_0 = (mul_((sub_(b, a)), (mul_(c, c))));
	let temp_21_1 = (sub_((mul_(b, (mul_(c, c)))), (mul_(a, (mul_(c, c))))));
	assert(eq_(temp_21_0, temp_21_1)) by {
		lemma_mul_dist(mul_(c, c), b, a);
	}
	let temp_22_0 = (mod_((mul_((mod_((mul_(d, b)), m)), (mul_(a, c)))), m));
	let temp_22_1 = (mod_((mul_((mod_((mul_(b, d)), m)), (mul_(a, c)))), m));
	assert(eq_(temp_22_0, temp_22_1)) by {
		lemma_mul_comm(d, b);
		cong_mod_(mul_(mod_(mul_(d, b), m), mul_(a, c)), m, mul_(mod_(mul_(b, d), m), mul_(a, c)), m);
		lemma_eq_ref(m);
		cong_mul_(mod_(mul_(d, b), m), mul_(a, c), mod_(mul_(b, d), m), mul_(a, c));
		lemma_eq_ref(mul_(a, c));
		cong_mod_(mul_(d, b), m, mul_(b, d), m);
	}
	let temp_23_0 = (mul_((mul_(b, a)), (mod_((mul_(c, d)), m))));
	let temp_23_1 = (mul_((mul_(b, a)), (mod_((mul_(d, c)), m))));
	assert(eq_(temp_23_0, temp_23_1)) by {
		lemma_mul_comm(c, d);
		cong_mul_(mul_(b, a), mod_(mul_(c, d), m), mul_(b, a), mod_(mul_(d, c), m));
		lemma_eq_ref(m);
		lemma_eq_ref(mul_(b, a));
		cong_mod_(mul_(c, d), m, mul_(d, c), m);
	}
	let temp_24_0 = (mul_((mul_(c, c)), (mul_(c, a))));
	let temp_24_1 = (mul_((mul_(c, a)), (mul_(c, c))));
	assert(eq_(temp_24_0, temp_24_1)) by {
		lemma_mul_comm(mul_(c, c), mul_(c, a));
	}
	let temp_25_0 = (mul_((mul_(d, c)), a));
	let temp_25_1 = (mul_((mul_(c, d)), a));
	assert(eq_(temp_25_0, temp_25_1)) by {
		lemma_eq_ref(a);
		cong_mul_(mul_(d, c), a, mul_(c, d), a);
		lemma_mul_comm(d, c);
	}
	let temp_26_0 = (mul_((mul_(b, b)), (mul_((mod_(d, m)), d))));
	let temp_26_1 = (mul_(b, (mul_(b, (mul_((mod_(d, m)), d))))));
	assert(eq_(temp_26_0, temp_26_1)) by {
		lemma_eq_sym(temp_26_1, temp_26_0);
		lemma_mul_assoc(b, b, mul_(mod_(d, m), d));
	}
	let temp_27_0 = (mul_((mul_(b, (mod_(c, m)))), (mul_(b, (mod_(c, m))))));
	let temp_27_1 = (mul_((mul_(b, (mod_((sub_(c, (mul_((mul_((add_(a, c)), (sub_(c, d)))), m)))), m)))), (mul_(b, (mod_(c, m))))));
	assert(eq_(temp_27_0, temp_27_1)) by {
		lemma_mod_mul_vanish(c, mul_(add_(a, c), sub_(c, d)), m);
		cong_mul_(mul_(b, mod_(c, m)), mul_(b, mod_(c, m)), mul_(b, mod_(sub_(c, mul_(mul_(add_(a, c), sub_(c, d)), m)), m)), mul_(b, mod_(c, m)));
		lemma_eq_ref(b);
		lemma_eq_sym(mul_(b, mod_(c, m)), mul_(b, mod_(sub_(c, mul_(mul_(add_(a, c), sub_(c, d)), m)), m)));
		cong_mul_(b, mod_(c, m), b, mod_(sub_(c, mul_(mul_(add_(a, c), sub_(c, d)), m)), m));
		lemma_eq_trans(mul_(b, mod_(c, m)), mul_(b, mod_(sub_(c, mul_(mul_(add_(a, c), sub_(c, d)), m)), m)), mul_(b, mod_(c, m)));
	}
	let temp_28_0 = (mul_((mul_(a, d)), (sub_(b, b))));
	let temp_28_1 = (mul_((sub_(b, b)), (mul_(a, d))));
	assert(eq_(temp_28_0, temp_28_1)) by {
		lemma_mul_comm(mul_(a, d), sub_(b, b));
	}
	let temp_29_0 = (mul_((mod_((mul_(c, b)), m)), (mul_(c, c))));
	let temp_29_1 = (mul_((mod_((add_((mul_((add_((mul_(d, a)), (mul_(d, a)))), m)), (mul_(c, b)))), m)), (mul_(c, c))));
	assert(eq_(temp_29_0, temp_29_1)) by {
		lemma_mul_comm(c, c);
		lemma_mod_mul_vanish(mul_(c, b), add_(mul_(d, a), mul_(d, a)), m);
		cong_mul_(mod_(mul_(c, b), m), mul_(c, c), mod_(add_(mul_(add_(mul_(d, a), mul_(d, a)), m), mul_(c, b)), m), mul_(c, c));
	}
	let temp_30_0 = (mul_((add_(d, b)), (mul_(c, c))));
	let temp_30_1 = (mul_((add_(b, d)), (mul_(c, c))));
	assert(eq_(temp_30_0, temp_30_1)) by {
		cong_mul_(add_(d, b), mul_(c, c), add_(b, d), mul_(c, c));
		lemma_add_comm(d, b);
		lemma_mul_comm(c, c);
	}
	let temp_31_0 = (mul_((add_(a, d)), (mul_(a, a))));
	let temp_31_1 = (add_((mul_(a, (mul_(a, a)))), (mul_(d, (mul_(a, a))))));
	assert(eq_(temp_31_0, temp_31_1)) by {
		lemma_mul_dist(a, d, mul_(a, a));
	}
	let temp_32_0 = (mul_((mul_(b, a)), (mod_((mul_(c, d)), m))));
	let temp_32_1 = (mul_(b, (mul_(a, (mod_((mul_(c, d)), m))))));
	assert(eq_(temp_32_0, temp_32_1)) by {
		lemma_mul_assoc(b, a, mod_(mul_(c, d), m));
		lemma_eq_sym(temp_32_1, temp_32_0);
	}
	let temp_33_0 = (mul_((mul_(a, (mod_(c, m)))), (mul_(c, b))));
	let temp_33_1 = (mul_((mul_(a, (mod_((sub_(c, (mul_((mul_((mul_(a, c)), (mul_(c, a)))), m)))), m)))), (mul_(c, b))));
	assert(eq_(temp_33_0, temp_33_1)) by {
		lemma_eq_ref(a);
		cong_mul_(a, mod_(c, m), a, mod_(sub_(c, mul_(mul_(mul_(a, c), mul_(c, a)), m)), m));
		lemma_eq_ref(mul_(c, b));
		lemma_mod_mul_vanish(c, mul_(mul_(a, c), mul_(c, a)), m);
		cong_mul_(mul_(a, mod_(c, m)), mul_(c, b), mul_(a, mod_(sub_(c, mul_(mul_(mul_(a, c), mul_(c, a)), m)), m)), mul_(c, b));
	}
	let temp_34_0 = (add_((mul_((mod_(d, m)), a)), (add_(c, d))));
	let temp_34_1 = (add_((mul_(a, (mod_(d, m)))), (add_(c, d))));
	assert(eq_(temp_34_0, temp_34_1)) by {
		lemma_mul_comm(mod_(d, m), a);
		cong_add_(mul_(mod_(d, m), a), add_(c, d), mul_(a, mod_(d, m)), add_(c, d));
		lemma_eq_ref(add_(c, d));
	}
	let temp_35_0 = (mul_((add_(c, as_elem(44))), (mul_(b, (mod_(b, m))))));
	let temp_35_1 = (mul_((mul_(b, (mod_(b, m)))), (add_(c, as_elem(44)))));
	assert(eq_(temp_35_0, temp_35_1)) by {
		lemma_mul_comm(add_(c, as_elem(44)), mul_(b, mod_(b, m)));
	}
	let temp_36_0 = (mul_((mul_(a, d)), (add_(b, b))));
	let temp_36_1 = (mul_((mul_(a, d)), (add_(b, b))));
	assert(eq_(temp_36_0, temp_36_1)) by {
		lemma_eq_ref(temp_36_0);
	}
	let temp_37_0 = (mul_((mul_(b, c)), (add_(a, c))));
	let temp_37_1 = (mul_((mul_(b, c)), (add_(c, a))));
	assert(eq_(temp_37_0, temp_37_1)) by {
		cong_mul_(mul_(b, c), add_(a, c), mul_(b, c), add_(c, a));
		lemma_add_comm(a, c);
		lemma_eq_ref(mul_(b, c));
	}
	let temp_38_0 = (mul_(b, (sub_(b, (mod_(d, m))))));
	let temp_38_1 = (mul_((sub_(b, (mod_(d, m)))), b));
	assert(eq_(temp_38_0, temp_38_1)) by {
		lemma_mul_comm(b, sub_(b, mod_(d, m)));
	}
	let temp_39_0 = (mul_((mul_(c, b)), (mul_(a, c))));
	let temp_39_1 = (mul_(c, (mul_(b, (mul_(a, c))))));
	assert(eq_(temp_39_0, temp_39_1)) by {
		lemma_eq_sym(temp_39_1, temp_39_0);
		lemma_mul_assoc(c, b, mul_(a, c));
	}
	let temp_40_0 = (add_((mul_(d, c)), (mul_(c, c))));
	let temp_40_1 = (mul_((add_(d, c)), c));
	assert(eq_(temp_40_0, temp_40_1)) by {
		lemma_eq_sym(temp_40_1, temp_40_0);
		lemma_mul_dist(d, c, c);
	}
	let temp_41_0 = (sub_((mod_((add_(a, b)), m)), (mul_(b, d))));
	let temp_41_1 = (sub_((mod_((add_(b, a)), m)), (mul_(b, d))));
	assert(eq_(temp_41_0, temp_41_1)) by {
		lemma_add_comm(a, b);
		cong_sub_(mod_(add_(a, b), m), mul_(b, d), mod_(add_(b, a), m), mul_(b, d));
		cong_mod_(add_(a, b), m, add_(b, a), m);
		lemma_eq_ref(mul_(b, d));
		lemma_eq_ref(m);
	}
	let temp_42_0 = (mul_((mul_(d, b)), (mul_(c, d))));
	let temp_42_1 = (mul_((mul_(c, d)), (mul_(d, b))));
	assert(eq_(temp_42_0, temp_42_1)) by {
		lemma_mul_comm(mul_(d, b), mul_(c, d));
	}
	let temp_43_0 = (mul_((mul_(a, b)), (mul_(d, d))));
	let temp_43_1 = (mul_((mul_(d, d)), (mul_(a, b))));
	assert(eq_(temp_43_0, temp_43_1)) by {
		lemma_mul_comm(mul_(a, b), mul_(d, d));
	}
	let temp_44_0 = (mul_((mul_(b, c)), (mod_((mul_(c, a)), m))));
	let temp_44_1 = (mul_((mul_(b, c)), (mod_((add_((mul_(c, a)), (mul_((sub_((mul_(b, a)), (mul_(a, d)))), m)))), m))));
	assert(eq_(temp_44_0, temp_44_1)) by {
		lemma_mod_mul_vanish(mul_(c, a), sub_(mul_(b, a), mul_(a, d)), m);
		cong_mul_(mul_(b, c), mod_(mul_(c, a), m), mul_(b, c), mod_(add_(mul_(c, a), mul_(sub_(mul_(b, a), mul_(a, d)), m)), m));
		lemma_eq_ref(mul_(b, c));
	}
	let temp_45_0 = (mul_((mul_(c, c)), (add_(c, b))));
	let temp_45_1 = (mul_(c, (mul_(c, (add_(c, b))))));
	assert(eq_(temp_45_0, temp_45_1)) by {
		lemma_eq_sym(temp_45_1, temp_45_0);
		lemma_mul_assoc(c, c, add_(c, b));
	}
	let temp_46_0 = (mul_((mul_(c, b)), (mul_(c, (mod_(c, m))))));
	let temp_46_1 = (mul_((mul_(c, b)), (mul_(c, (mod_((add_(c, (mul_((mod_((mul_((mul_(d, c)), (sub_(b, a)))), m)), m)))), m))))));
	assert(eq_(temp_46_0, temp_46_1)) by {
		lemma_mod_mul_vanish(c, mod_(mul_(mul_(d, c), sub_(b, a)), m), m);
		cong_mul_(mul_(c, b), mul_(c, mod_(c, m)), mul_(c, b), mul_(c, mod_(add_(c, mul_(mod_(mul_(mul_(d, c), sub_(b, a)), m), m)), m)));
		lemma_eq_ref(c);
		lemma_eq_ref(mul_(c, b));
		cong_mul_(c, mod_(c, m), c, mod_(add_(c, mul_(mod_(mul_(mul_(d, c), sub_(b, a)), m), m)), m));
	}
	let temp_47_0 = (mul_((mul_(c, b)), (mul_(b, b))));
	let temp_47_1 = (mul_((mul_((mul_(c, b)), b)), b));
	assert(eq_(temp_47_0, temp_47_1)) by {
		lemma_mul_assoc(mul_(c, b), b, b);
	}
	let temp_48_0 = (mul_((mul_(d, as_elem(58))), (sub_(b, c))));
	let temp_48_1 = (mul_(d, (mul_(as_elem(58), (sub_(b, c))))));
	assert(eq_(temp_48_0, temp_48_1)) by {
		lemma_mul_assoc(d, as_elem(58), sub_(b, c));
		lemma_eq_sym(temp_48_1, temp_48_0);
	}
	let temp_49_0 = (mul_((mul_(a, c)), (mul_(a, d))));
	let temp_49_1 = (mul_((mul_(c, a)), (mul_(a, d))));
	assert(eq_(temp_49_0, temp_49_1)) by {
		cong_mul_(mul_(a, c), mul_(a, d), mul_(c, a), mul_(a, d));
		lemma_mul_comm(a, c);
		lemma_eq_ref(mul_(a, d));
	}
	let temp_50_0 = (mul_((mul_(a, a)), (mul_(a, c))));
	let temp_50_1 = (mul_((mul_(a, c)), (mul_(a, a))));
	assert(eq_(temp_50_0, temp_50_1)) by {
		lemma_mul_comm(mul_(a, a), mul_(a, c));
	}
	let temp_51_0 = (sub_((mul_((mod_(c, m)), c)), (mul_(b, b))));
	let temp_51_1 = (sub_((mul_((mod_((sub_(c, (mul_((add_(a, (mod_((mul_(d, a)), m)))), m)))), m)), c)), (mul_(b, b))));
	assert(eq_(temp_51_0, temp_51_1)) by {
		lemma_mul_comm(b, b);
		lemma_mod_mul_vanish(c, add_(a, mod_(mul_(d, a), m)), m);
		cong_sub_(mul_(mod_(c, m), c), mul_(b, b), mul_(mod_(sub_(c, mul_(add_(a, mod_(mul_(d, a), m)), m)), m), c), mul_(b, b));
		cong_mul_(mod_(c, m), c, mod_(sub_(c, mul_(add_(a, mod_(mul_(d, a), m)), m)), m), c);
		lemma_eq_ref(c);
	}
	let temp_52_0 = (mul_((mul_(d, b)), (sub_(a, d))));
	let temp_52_1 = (mul_(d, (mul_(b, (sub_(a, d))))));
	assert(eq_(temp_52_0, temp_52_1)) by {
		lemma_eq_sym(temp_52_1, temp_52_0);
		lemma_mul_assoc(d, b, sub_(a, d));
	}
	let temp_53_0 = (mul_((mod_((mul_(a, b)), m)), (mul_(d, c))));
	let temp_53_1 = (mul_((mod_((mul_(a, b)), m)), (mul_(c, d))));
	assert(eq_(temp_53_0, temp_53_1)) by {
		lemma_mul_comm(d, c);
		cong_mul_(mod_(mul_(a, b), m), mul_(d, c), mod_(mul_(a, b), m), mul_(c, d));
		lemma_eq_ref(mod_(mul_(a, b), m));
	}
	let temp_54_0 = (mul_((mul_(b, b)), (add_(c, d))));
	let temp_54_1 = (mul_((mul_(b, b)), (add_(d, c))));
	assert(eq_(temp_54_0, temp_54_1)) by {
		cong_mul_(mul_(b, b), add_(c, d), mul_(b, b), add_(d, c));
		lemma_add_comm(c, d);
		lemma_mul_comm(b, b);
	}
	let temp_55_0 = (mul_((sub_(c, a)), (sub_(b, (mod_(a, m))))));
	let temp_55_1 = (sub_((mul_(c, (sub_(b, (mod_(a, m)))))), (mul_(a, (sub_(b, (mod_(a, m))))))));
	assert(eq_(temp_55_0, temp_55_1)) by {
		lemma_mul_dist(sub_(b, mod_(a, m)), c, a);
	}
	let temp_56_0 = (mul_((mul_(b, b)), (mul_(as_elem(31), a))));
	let temp_56_1 = (mul_((mul_(b, b)), (mul_(a, as_elem(31)))));
	assert(eq_(temp_56_0, temp_56_1)) by {
		cong_mul_(mul_(b, b), mul_(as_elem(31), a), mul_(b, b), mul_(a, as_elem(31)));
		lemma_mul_comm(b, b);
		lemma_mul_comm(as_elem(31), a);
	}
	let temp_57_0 = (mul_((mul_(d, c)), (mul_(c, a))));
	let temp_57_1 = (mul_((mul_((mul_(d, c)), c)), a));
	assert(eq_(temp_57_0, temp_57_1)) by {
		lemma_mul_assoc(mul_(d, c), c, a);
	}
	let temp_58_0 = (mul_((mul_(a, c)), (mul_(d, a))));
	let temp_58_1 = (mul_((mul_(d, a)), (mul_(a, c))));
	assert(eq_(temp_58_0, temp_58_1)) by {
		lemma_mul_comm(mul_(a, c), mul_(d, a));
	}
	let temp_59_0 = (mul_((mul_(c, d)), (mul_(b, a))));
	let temp_59_1 = (mul_((mul_(d, c)), (mul_(b, a))));
	assert(eq_(temp_59_0, temp_59_1)) by {
		cong_mul_(mul_(c, d), mul_(b, a), mul_(d, c), mul_(b, a));
		lemma_mul_comm(c, d);
		lemma_eq_ref(mul_(b, a));
	}
	let temp_60_0 = (mul_((mul_(a, (mod_(c, m)))), c));
	let temp_60_1 = (mul_((mul_((mod_(c, m)), a)), c));
	assert(eq_(temp_60_0, temp_60_1)) by {
		cong_mul_(mul_(a, mod_(c, m)), c, mul_(mod_(c, m), a), c);
		lemma_mul_comm(a, mod_(c, m));
		lemma_eq_ref(c);
	}
	let temp_61_0 = (mul_((mul_((mod_(d, m)), c)), (sub_(d, b))));
	let temp_61_1 = (mul_((sub_(d, b)), (mul_((mod_(d, m)), c))));
	assert(eq_(temp_61_0, temp_61_1)) by {
		lemma_mul_comm(mul_(mod_(d, m), c), sub_(d, b));
	}
	let temp_62_0 = (mod_((mul_((mul_(c, c)), (mod_((mul_(b, c)), m)))), m));
	let temp_62_1 = (mod_((mul_((mul_(c, c)), (mod_((add_((mul_(b, c)), (mul_((add_((mul_(b, b)), (mul_(b, c)))), m)))), m)))), m));
	assert(eq_(temp_62_0, temp_62_1)) by {
		lemma_mul_comm(c, c);
		lemma_mod_mul_vanish(mul_(b, c), add_(mul_(b, b), mul_(b, c)), m);
		cong_mod_(mul_(mul_(c, c), mod_(mul_(b, c), m)), m, mul_(mul_(c, c), mod_(add_(mul_(b, c), mul_(add_(mul_(b, b), mul_(b, c)), m)), m)), m);
		lemma_eq_ref(m);
		cong_mul_(mul_(c, c), mod_(mul_(b, c), m), mul_(c, c), mod_(add_(mul_(b, c), mul_(add_(mul_(b, b), mul_(b, c)), m)), m));
	}
	let temp_63_0 = (mul_((mul_(d, a)), (mul_((mod_(as_elem(4), m)), b))));
	let temp_63_1 = (mul_((mul_((mod_(as_elem(4), m)), b)), (mul_(d, a))));
	assert(eq_(temp_63_0, temp_63_1)) by {
		lemma_mul_comm(mul_(d, a), mul_(mod_(as_elem(4), m), b));
	}
	let temp_64_0 = (mul_((mul_(b, (mod_(a, m)))), (mul_(b, b))));
	let temp_64_1 = (mul_((mul_(b, (mod_((add_((mul_((sub_((mul_(b, d)), (mul_(b, b)))), m)), a)), m)))), (mul_(b, b))));
	assert(eq_(temp_64_0, temp_64_1)) by {
		lemma_mul_comm(b, b);
		lemma_mod_mul_vanish(a, sub_(mul_(b, d), mul_(b, b)), m);
		cong_mul_(mul_(b, mod_(a, m)), mul_(b, b), mul_(b, mod_(add_(mul_(sub_(mul_(b, d), mul_(b, b)), m), a), m)), mul_(b, b));
		lemma_eq_ref(b);
		cong_mul_(b, mod_(a, m), b, mod_(add_(mul_(sub_(mul_(b, d), mul_(b, b)), m), a), m));
	}
	let temp_65_0 = (mul_((mul_(b, a)), b));
	let temp_65_1 = (mul_((mul_(a, b)), b));
	assert(eq_(temp_65_0, temp_65_1)) by {
		cong_mul_(mul_(b, a), b, mul_(a, b), b);
		lemma_mul_comm(b, a);
		lemma_eq_ref(b);
	}
	let temp_66_0 = (mul_((mod_((mul_(c, c)), m)), (mul_(a, c))));
	let temp_66_1 = (mul_((mod_((sub_((mul_(c, c)), (mul_((mul_((mul_(b, b)), (mod_((mul_(d, (mod_(b, m)))), m)))), m)))), m)), (mul_(a, c))));
	assert(eq_(temp_66_0, temp_66_1)) by {
		lemma_mod_mul_vanish(mul_(c, c), mul_(mul_(b, b), mod_(mul_(d, mod_(b, m)), m)), m);
		cong_mul_(mod_(mul_(c, c), m), mul_(a, c), mod_(sub_(mul_(c, c), mul_(mul_(mul_(b, b), mod_(mul_(d, mod_(b, m)), m)), m)), m), mul_(a, c));
		lemma_eq_ref(mul_(a, c));
	}
	let temp_67_0 = (mul_((mul_(c, c)), (mul_(b, c))));
	let temp_67_1 = (mul_(c, (mul_(c, (mul_(b, c))))));
	assert(eq_(temp_67_0, temp_67_1)) by {
		lemma_eq_sym(temp_67_1, temp_67_0);
		lemma_mul_assoc(c, c, mul_(b, c));
	}
	let temp_68_0 = (mod_((mul_(d, (add_(d, b)))), m));
	let temp_68_1 = (mod_((add_((mul_(d, (add_(d, b)))), (mul_((mul_((mul_(a, a)), (mul_(d, a)))), m)))), m));
	assert(eq_(temp_68_0, temp_68_1)) by {
		lemma_mod_mul_vanish(mul_(d, add_(d, b)), mul_(mul_(a, a), mul_(d, a)), m);
	}
	let temp_69_0 = (mod_((mul_((mul_(b, b)), (sub_(c, c)))), m));
	let temp_69_1 = (mod_((mul_(b, (mul_(b, (sub_(c, c)))))), m));
	assert(eq_(temp_69_0, temp_69_1)) by {
		lemma_mul_assoc(b, b, sub_(c, c));
		cong_mod_(mul_(mul_(b, b), sub_(c, c)), m, mul_(b, mul_(b, sub_(c, c))), m);
		lemma_eq_sym(mul_(b, mul_(b, sub_(c, c))), mul_(mul_(b, b), sub_(c, c)));
		lemma_eq_ref(m);
	}
	let temp_70_0 = (sub_((mul_(a, a)), (add_((mod_(a, m)), b))));
	let temp_70_1 = (sub_((mul_(a, a)), (add_(b, (mod_(a, m))))));
	assert(eq_(temp_70_0, temp_70_1)) by {
		lemma_add_comm(mod_(a, m), b);
		cong_sub_(mul_(a, a), add_(mod_(a, m), b), mul_(a, a), add_(b, mod_(a, m)));
		lemma_mul_comm(a, a);
	}
	let temp_71_0 = (mul_((sub_(a, (mod_(b, m)))), (mul_(a, c))));
	let temp_71_1 = (mul_((mul_((sub_(a, (mod_(b, m)))), a)), c));
	assert(eq_(temp_71_0, temp_71_1)) by {
		lemma_mul_assoc(sub_(a, mod_(b, m)), a, c);
	}
	let temp_72_0 = (mul_((mod_((mul_(c, d)), m)), (mod_((mul_((mod_(b, m)), a)), m))));
	let temp_72_1 = (mul_((mod_((sub_((mul_(c, d)), (mul_((mul_((add_(c, b)), (mul_(b, a)))), m)))), m)), (mod_((mul_((mod_(b, m)), a)), m))));
	assert(eq_(temp_72_0, temp_72_1)) by {
		lemma_eq_ref(mod_(mul_(mod_(b, m), a), m));
		lemma_mod_mul_vanish(mul_(c, d), mul_(add_(c, b), mul_(b, a)), m);
		cong_mul_(mod_(mul_(c, d), m), mod_(mul_(mod_(b, m), a), m), mod_(sub_(mul_(c, d), mul_(mul_(add_(c, b), mul_(b, a)), m)), m), mod_(mul_(mod_(b, m), a), m));
	}
	let temp_73_0 = (mul_((mul_((mod_(c, m)), c)), (add_(d, b))));
	let temp_73_1 = (add_((mul_((mul_((mod_(c, m)), c)), d)), (mul_((mul_((mod_(c, m)), c)), b))));
	assert(eq_(temp_73_0, temp_73_1)) by {
		lemma_mul_dist(mul_(mod_(c, m), c), d, b);
	}
	let temp_74_0 = (mul_((mul_(c, a)), (mul_(b, b))));
	let temp_74_1 = (mul_((mul_((mul_(c, a)), b)), b));
	assert(eq_(temp_74_0, temp_74_1)) by {
		lemma_mul_assoc(mul_(c, a), b, b);
	}
	let temp_75_0 = (mul_((sub_(c, c)), (mul_(c, a))));
	let temp_75_1 = (sub_((mul_(c, (mul_(c, a)))), (mul_(c, (mul_(c, a))))));
	assert(eq_(temp_75_0, temp_75_1)) by {
		lemma_mul_dist(mul_(c, a), c, c);
	}
	let temp_76_0 = (mul_((mul_(d, c)), (mul_(c, d))));
	let temp_76_1 = (mul_((mul_(c, d)), (mul_(c, d))));
	assert(eq_(temp_76_0, temp_76_1)) by {
		cong_mul_(mul_(d, c), mul_(c, d), mul_(c, d), mul_(c, d));
		lemma_mul_comm(d, c);
		lemma_eq_ref(mul_(c, d));
	}
	let temp_77_0 = (sub_((mul_(c, c)), (sub_(c, a))));
	let temp_77_1 = (sub_((mul_(c, c)), (sub_(c, a))));
	assert(eq_(temp_77_0, temp_77_1)) by {
		lemma_eq_ref(temp_77_0);
	}
	let temp_78_0 = (mul_((sub_((mod_(a, m)), c)), c));
	let temp_78_1 = (mul_(c, (sub_((mod_(a, m)), c))));
	assert(eq_(temp_78_0, temp_78_1)) by {
		lemma_mul_comm(sub_(mod_(a, m), c), c);
	}
	let temp_79_0 = (mod_((mul_((mod_((mul_(d, c)), m)), (mul_(a, d)))), m));
	let temp_79_1 = (mod_((mul_((mod_((mul_(c, d)), m)), (mul_(a, d)))), m));
	assert(eq_(temp_79_0, temp_79_1)) by {
		lemma_mul_comm(d, c);
		cong_mod_(mul_(mod_(mul_(d, c), m), mul_(a, d)), m, mul_(mod_(mul_(c, d), m), mul_(a, d)), m);
		lemma_eq_ref(m);
		cong_mul_(mod_(mul_(d, c), m), mul_(a, d), mod_(mul_(c, d), m), mul_(a, d));
		lemma_eq_ref(mul_(a, d));
		cong_mod_(mul_(d, c), m, mul_(c, d), m);
	}
	let temp_80_0 = (mul_((sub_(b, a)), (mul_(c, c))));
	let temp_80_1 = (mul_((mul_((sub_(b, a)), c)), c));
	assert(eq_(temp_80_0, temp_80_1)) by {
		lemma_mul_assoc(sub_(b, a), c, c);
	}
	let temp_81_0 = (mul_((mod_((mul_(b, a)), m)), (mul_(a, (mod_(b, m))))));
	let temp_81_1 = (mul_((mul_((mod_((mul_(b, a)), m)), a)), (mod_(b, m))));
	assert(eq_(temp_81_0, temp_81_1)) by {
		lemma_mul_assoc(mod_(mul_(b, a), m), a, mod_(b, m));
	}
	let temp_82_0 = (mul_((mul_(d, c)), (mul_(d, a))));
	let temp_82_1 = (mul_((mul_((mul_(d, c)), d)), a));
	assert(eq_(temp_82_0, temp_82_1)) by {
		lemma_mul_assoc(mul_(d, c), d, a);
	}
	let temp_83_0 = (mul_((mul_(a, (mod_(b, m)))), (mul_(c, b))));
	let temp_83_1 = (mul_((mul_(a, (mod_((add_((mul_((mul_((mod_((mul_(b, d)), m)), (mul_(a, b)))), m)), b)), m)))), (mul_(c, b))));
	assert(eq_(temp_83_0, temp_83_1)) by {
		cong_mul_(a, mod_(b, m), a, mod_(add_(mul_(mul_(mod_(mul_(b, d), m), mul_(a, b)), m), b), m));
		lemma_eq_ref(mul_(c, b));
		lemma_eq_ref(a);
		lemma_mod_mul_vanish(b, mul_(mod_(mul_(b, d), m), mul_(a, b)), m);
		cong_mul_(mul_(a, mod_(b, m)), mul_(c, b), mul_(a, mod_(add_(mul_(mul_(mod_(mul_(b, d), m), mul_(a, b)), m), b), m)), mul_(c, b));
	}
	let temp_84_0 = (mul_((mul_((mod_(b, m)), a)), (mul_(a, c))));
	let temp_84_1 = (mul_((mul_(a, c)), (mul_((mod_(b, m)), a))));
	assert(eq_(temp_84_0, temp_84_1)) by {
		lemma_mul_comm(mul_(mod_(b, m), a), mul_(a, c));
	}
	let temp_85_0 = (mul_((sub_((mod_(b, m)), d)), (mul_(b, b))));
	let temp_85_1 = (mul_((sub_((mod_(b, m)), d)), (mul_(b, b))));
	assert(eq_(temp_85_0, temp_85_1)) by {
		lemma_eq_ref(temp_85_0);
	}
	let temp_86_0 = (mul_((mul_(d, a)), (mul_(d, d))));
	let temp_86_1 = (mul_(d, (mul_(a, (mul_(d, d))))));
	assert(eq_(temp_86_0, temp_86_1)) by {
		lemma_eq_sym(temp_86_1, temp_86_0);
		lemma_mul_assoc(d, a, mul_(d, d));
	}
	let temp_87_0 = (add_((mul_((mod_(d, m)), c)), (mul_(b, a))));
	let temp_87_1 = (add_((mul_(b, a)), (mul_((mod_(d, m)), c))));
	assert(eq_(temp_87_0, temp_87_1)) by {
		lemma_add_comm(mul_(mod_(d, m), c), mul_(b, a));
	}
	let temp_88_0 = (mul_((mul_(d, c)), (mul_(c, c))));
	let temp_88_1 = (mul_((mul_(c, c)), (mul_(d, c))));
	assert(eq_(temp_88_0, temp_88_1)) by {
		lemma_mul_comm(mul_(d, c), mul_(c, c));
	}
	let temp_89_0 = (mul_((mul_((mod_(b, m)), d)), (mul_(a, a))));
	let temp_89_1 = (mul_((mul_((mod_((add_((mul_((mul_((mul_(d, b)), (mul_(c, a)))), m)), b)), m)), d)), (mul_(a, a))));
	assert(eq_(temp_89_0, temp_89_1)) by {
		lemma_mul_comm(a, a);
		lemma_mod_mul_vanish(b, mul_(mul_(d, b), mul_(c, a)), m);
		cong_mul_(mul_(mod_(b, m), d), mul_(a, a), mul_(mod_(add_(mul_(mul_(mul_(d, b), mul_(c, a)), m), b), m), d), mul_(a, a));
		lemma_eq_ref(d);
		cong_mul_(mod_(b, m), d, mod_(add_(mul_(mul_(mul_(d, b), mul_(c, a)), m), b), m), d);
	}
	let temp_90_0 = (mod_((mul_((mul_(c, b)), (mul_(a, a)))), m));
	let temp_90_1 = (mod_((mul_((mul_(a, a)), (mul_(c, b)))), m));
	assert(eq_(temp_90_0, temp_90_1)) by {
		lemma_mul_comm(mul_(c, b), mul_(a, a));
		cong_mod_(mul_(mul_(c, b), mul_(a, a)), m, mul_(mul_(a, a), mul_(c, b)), m);
		lemma_eq_ref(m);
	}
	let temp_91_0 = (mul_((mul_(a, (mod_(c, m)))), (mul_(a, b))));
	let temp_91_1 = (mul_(a, (mul_((mod_(c, m)), (mul_(a, b))))));
	assert(eq_(temp_91_0, temp_91_1)) by {
		lemma_mul_assoc(a, mod_(c, m), mul_(a, b));
		lemma_eq_sym(temp_91_1, temp_91_0);
	}
	let temp_92_0 = (add_((mul_((mod_(b, m)), b)), (mod_((mul_(c, c)), m))));
	let temp_92_1 = (add_((mul_((mod_(b, m)), b)), (mod_((sub_((mul_(c, c)), (mul_((mul_((sub_(c, a)), (sub_(a, d)))), m)))), m))));
	assert(eq_(temp_92_0, temp_92_1)) by {
		lemma_mod_mul_vanish(mul_(c, c), mul_(sub_(c, a), sub_(a, d)), m);
		cong_add_(mul_(mod_(b, m), b), mod_(mul_(c, c), m), mul_(mod_(b, m), b), mod_(sub_(mul_(c, c), mul_(mul_(sub_(c, a), sub_(a, d)), m)), m));
		lemma_eq_ref(mul_(mod_(b, m), b));
	}
	let temp_93_0 = (mod_((mul_((mul_(b, as_elem(2))), (mul_((mod_(b, m)), a)))), m));
	let temp_93_1 = (mod_((mul_(b, (mul_(as_elem(2), (mul_((mod_(b, m)), a)))))), m));
	assert(eq_(temp_93_0, temp_93_1)) by {
		lemma_mul_assoc(b, as_elem(2), mul_(mod_(b, m), a));
		cong_mod_(mul_(mul_(b, as_elem(2)), mul_(mod_(b, m), a)), m, mul_(b, mul_(as_elem(2), mul_(mod_(b, m), a))), m);
		lemma_eq_sym(mul_(b, mul_(as_elem(2), mul_(mod_(b, m), a))), mul_(mul_(b, as_elem(2)), mul_(mod_(b, m), a)));
		lemma_eq_ref(m);
	}
	let temp_94_0 = (mul_((mul_(a, a)), (mul_(c, c))));
	let temp_94_1 = (mul_((mul_((mul_(a, a)), c)), c));
	assert(eq_(temp_94_0, temp_94_1)) by {
		lemma_mul_assoc(mul_(a, a), c, c);
	}
	let temp_95_0 = (mod_((mul_((add_(a, c)), (sub_(d, a)))), m));
	let temp_95_1 = (mod_((add_((mul_(a, (sub_(d, a)))), (mul_(c, (sub_(d, a)))))), m));
	assert(eq_(temp_95_0, temp_95_1)) by {
		lemma_mul_dist(a, c, sub_(d, a));
		cong_mod_(mul_(add_(a, c), sub_(d, a)), m, add_(mul_(a, sub_(d, a)), mul_(c, sub_(d, a))), m);
		lemma_eq_ref(m);
	}
	let temp_96_0 = (mul_((mul_(c, b)), (mul_(b, d))));
	let temp_96_1 = (mul_((mul_(c, b)), (mul_(d, b))));
	assert(eq_(temp_96_0, temp_96_1)) by {
		cong_mul_(mul_(c, b), mul_(b, d), mul_(c, b), mul_(d, b));
		lemma_mul_comm(b, d);
		lemma_eq_ref(mul_(c, b));
	}
	let temp_97_0 = (mul_((mul_(a, d)), (mul_(b, b))));
	let temp_97_1 = (mul_((mul_(b, b)), (mul_(a, d))));
	assert(eq_(temp_97_0, temp_97_1)) by {
		lemma_mul_comm(mul_(a, d), mul_(b, b));
	}
	let temp_98_0 = (mod_((sub_((mul_(a, a)), (mul_(a, d)))), m));
	let temp_98_1 = (mod_((sub_((mod_((mul_(a, a)), m)), (mul_(a, d)))), m));
	assert(eq_(temp_98_0, temp_98_1)) by {
		lemma_mod_sub_noop(mul_(a, a), mul_(a, d), m);
	}
	let temp_99_0 = (add_((mul_(d, d)), (sub_(d, b))));
	let temp_99_1 = (add_((mul_(d, d)), (sub_(d, b))));
	assert(eq_(temp_99_0, temp_99_1)) by {
		lemma_eq_ref(temp_99_0);
	}
	let temp_100_0 = (mul_((mul_(a, b)), (mul_(c, d))));
	let temp_100_1 = (mul_((mul_(a, b)), (mul_(d, c))));
	assert(eq_(temp_100_0, temp_100_1)) by {
		cong_mul_(mul_(a, b), mul_(c, d), mul_(a, b), mul_(d, c));
		lemma_mul_comm(c, d);
		lemma_eq_ref(mul_(a, b));
	}
	let temp_101_0 = (mul_((mod_((mul_(b, d)), m)), (add_(d, a))));
	let temp_101_1 = (add_((mul_((mod_((mul_(b, d)), m)), d)), (mul_((mod_((mul_(b, d)), m)), a))));
	assert(eq_(temp_101_0, temp_101_1)) by {
		lemma_mul_dist(mod_(mul_(b, d), m), d, a);
	}
	let temp_102_0 = (mul_((mul_(c, c)), (mul_(c, d))));
	let temp_102_1 = (mul_(c, (mul_(c, (mul_(c, d))))));
	assert(eq_(temp_102_0, temp_102_1)) by {
		lemma_eq_sym(temp_102_1, temp_102_0);
		lemma_mul_assoc(c, c, mul_(c, d));
	}
	let temp_103_0 = (mul_((mul_(d, b)), (mod_((add_(a, b)), m))));
	let temp_103_1 = (mul_((mul_(d, b)), (mod_((sub_((add_(a, b)), (mul_((mul_((add_(a, b)), (mul_(b, c)))), m)))), m))));
	assert(eq_(temp_103_0, temp_103_1)) by {
		lemma_mod_mul_vanish(add_(a, b), mul_(add_(a, b), mul_(b, c)), m);
		cong_mul_(mul_(d, b), mod_(add_(a, b), m), mul_(d, b), mod_(sub_(add_(a, b), mul_(mul_(add_(a, b), mul_(b, c)), m)), m));
		lemma_eq_ref(mul_(d, b));
	}
	let temp_104_0 = (mul_((mod_((mul_(d, b)), m)), (sub_(b, c))));
	let temp_104_1 = (mul_((sub_(b, c)), (mod_((mul_(d, b)), m))));
	assert(eq_(temp_104_0, temp_104_1)) by {
		lemma_mul_comm(mod_(mul_(d, b), m), sub_(b, c));
	}
	let temp_105_0 = (mul_((mul_(c, d)), (mul_(b, d))));
	let temp_105_1 = (mul_(c, (mul_(d, (mul_(b, d))))));
	assert(eq_(temp_105_0, temp_105_1)) by {
		lemma_eq_sym(temp_105_1, temp_105_0);
		lemma_mul_assoc(c, d, mul_(b, d));
	}
	let temp_106_0 = (mul_((mul_(b, c)), (mul_(a, (mod_(b, m))))));
	let temp_106_1 = (mul_(b, (mul_(c, (mul_(a, (mod_(b, m))))))));
	assert(eq_(temp_106_0, temp_106_1)) by {
		lemma_mul_assoc(b, c, mul_(a, mod_(b, m)));
		lemma_eq_sym(temp_106_1, temp_106_0);
	}
	let temp_107_0 = (mul_((mul_(d, b)), (sub_(a, a))));
	let temp_107_1 = (mul_(d, (mul_(b, (sub_(a, a))))));
	assert(eq_(temp_107_0, temp_107_1)) by {
		lemma_eq_sym(temp_107_1, temp_107_0);
		lemma_mul_assoc(d, b, sub_(a, a));
	}
	let temp_108_0 = (mul_((mul_(b, d)), (mul_(d, (mod_(a, m))))));
	let temp_108_1 = (mul_((mul_(b, d)), (mul_((mod_(a, m)), d))));
	assert(eq_(temp_108_0, temp_108_1)) by {
		lemma_mul_comm(d, mod_(a, m));
		cong_mul_(mul_(b, d), mul_(d, mod_(a, m)), mul_(b, d), mul_(mod_(a, m), d));
		lemma_eq_ref(mul_(b, d));
	}
	let temp_109_0 = (mul_((mul_(c, a)), (mul_(a, c))));
	let temp_109_1 = (mul_(c, (mul_(a, (mul_(a, c))))));
	assert(eq_(temp_109_0, temp_109_1)) by {
		lemma_eq_sym(temp_109_1, temp_109_0);
		lemma_mul_assoc(c, a, mul_(a, c));
	}
	let temp_110_0 = (mul_((add_(b, d)), (mod_((mul_(b, (mod_(b, m)))), m))));
	let temp_110_1 = (mul_((add_(b, d)), (mod_((mod_((mul_(b, b)), m)), m))));
	assert(eq_(temp_110_0, temp_110_1)) by {
		lemma_mod_mul_noop(b, b, m);
		cong_mul_(add_(b, d), mod_(mul_(b, mod_(b, m)), m), add_(b, d), mod_(mod_(mul_(b, b), m), m));
		lemma_eq_sym(mod_(mod_(mul_(b, b), m), m), mod_(mul_(b, mod_(b, m)), m));
		lemma_eq_ref(add_(b, d));
	}
	let temp_111_0 = (mul_((mul_(d, a)), (mul_(a, b))));
	let temp_111_1 = (mul_(d, (mul_(a, (mul_(a, b))))));
	assert(eq_(temp_111_0, temp_111_1)) by {
		lemma_eq_sym(temp_111_1, temp_111_0);
		lemma_mul_assoc(d, a, mul_(a, b));
	}
	let temp_112_0 = (mul_((mul_(d, c)), (mul_(a, c))));
	let temp_112_1 = (mul_((mul_(a, c)), (mul_(d, c))));
	assert(eq_(temp_112_0, temp_112_1)) by {
		lemma_mul_comm(mul_(d, c), mul_(a, c));
	}
	let temp_113_0 = (mul_((add_(a, c)), (mul_((mod_(c, m)), c))));
	let temp_113_1 = (mul_((add_(a, c)), (mul_((mod_((sub_(c, (mul_((mod_((mul_((mul_(b, as_elem(1))), (mod_((mul_(a, a)), m)))), m)), m)))), m)), c))));
	assert(eq_(temp_113_0, temp_113_1)) by {
		lemma_mod_mul_vanish(c, mod_(mul_(mul_(b, as_elem(1)), mod_(mul_(a, a), m)), m), m);
		cong_mul_(add_(a, c), mul_(mod_(c, m), c), add_(a, c), mul_(mod_(sub_(c, mul_(mod_(mul_(mul_(b, as_elem(1)), mod_(mul_(a, a), m)), m), m)), m), c));
		lemma_eq_ref(c);
		lemma_eq_ref(add_(a, c));
		cong_mul_(mod_(c, m), c, mod_(sub_(c, mul_(mod_(mul_(mul_(b, as_elem(1)), mod_(mul_(a, a), m)), m), m)), m), c);
	}
	let temp_114_0 = (mul_((mul_(a, a)), (mul_(a, c))));
	let temp_114_1 = (mul_((mul_(a, c)), (mul_(a, a))));
	assert(eq_(temp_114_0, temp_114_1)) by {
		lemma_mul_comm(mul_(a, a), mul_(a, c));
	}
	let temp_115_0 = (mul_((mul_(c, b)), a));
	let temp_115_1 = (mul_(c, (mul_(b, a))));
	assert(eq_(temp_115_0, temp_115_1)) by {
		lemma_eq_sym(temp_115_1, temp_115_0);
		lemma_mul_assoc(c, b, a);
	}
	let temp_116_0 = (mul_((mul_(c, d)), (mul_(a, (mod_(c, m))))));
	let temp_116_1 = (mul_((mul_((mul_(c, d)), a)), (mod_(c, m))));
	assert(eq_(temp_116_0, temp_116_1)) by {
		lemma_mul_assoc(mul_(c, d), a, mod_(c, m));
	}
	let temp_117_0 = (mul_((mod_((mul_(d, d)), m)), (mul_(c, d))));
	let temp_117_1 = (mul_((mod_((mul_(d, d)), m)), (mul_(d, c))));
	assert(eq_(temp_117_0, temp_117_1)) by {
		cong_mul_(mod_(mul_(d, d), m), mul_(c, d), mod_(mul_(d, d), m), mul_(d, c));
		lemma_mul_comm(c, d);
		lemma_eq_ref(mod_(mul_(d, d), m));
	}
	let temp_118_0 = (mul_((mul_(b, as_elem(39))), (mul_(d, c))));
	let temp_118_1 = (mul_((mul_(b, as_elem(39))), (mul_(c, d))));
	assert(eq_(temp_118_0, temp_118_1)) by {
		lemma_mul_comm(d, c);
		cong_mul_(mul_(b, as_elem(39)), mul_(d, c), mul_(b, as_elem(39)), mul_(c, d));
		lemma_eq_ref(mul_(b, as_elem(39)));
	}
	let temp_119_0 = (sub_((mul_(d, a)), (mul_(a, b))));
	let temp_119_1 = (sub_((mul_(a, d)), (mul_(a, b))));
	assert(eq_(temp_119_0, temp_119_1)) by {
		cong_sub_(mul_(d, a), mul_(a, b), mul_(a, d), mul_(a, b));
		lemma_mul_comm(d, a);
		lemma_eq_ref(mul_(a, b));
	}
	let temp_120_0 = (mul_((mul_(b, b)), (mul_(d, c))));
	let temp_120_1 = (mul_((mul_(b, b)), (mul_(d, c))));
	assert(eq_(temp_120_0, temp_120_1)) by {
		lemma_eq_ref(temp_120_0);
	}
	let temp_121_0 = (mul_((mul_(c, d)), (mul_(d, a))));
	let temp_121_1 = (mul_(c, (mul_(d, (mul_(d, a))))));
	assert(eq_(temp_121_0, temp_121_1)) by {
		lemma_eq_sym(temp_121_1, temp_121_0);
		lemma_mul_assoc(c, d, mul_(d, a));
	}
	let temp_122_0 = (add_((sub_(b, d)), (mul_(b, d))));
	let temp_122_1 = (add_((mul_(b, d)), (sub_(b, d))));
	assert(eq_(temp_122_0, temp_122_1)) by {
		lemma_add_comm(sub_(b, d), mul_(b, d));
	}
	let temp_123_0 = (sub_((mod_((sub_(a, a)), m)), (mul_(d, d))));
	let temp_123_1 = (sub_((mod_((sub_((mod_(a, m)), a)), m)), (mul_(d, d))));
	assert(eq_(temp_123_0, temp_123_1)) by {
		lemma_mul_comm(d, d);
		cong_sub_(mod_(sub_(a, a), m), mul_(d, d), mod_(sub_(mod_(a, m), a), m), mul_(d, d));
		lemma_mod_sub_noop(a, a, m);
	}
	let temp_124_0 = (mul_((mul_(d, a)), (mul_(c, d))));
	let temp_124_1 = (mul_(d, (mul_(a, (mul_(c, d))))));
	assert(eq_(temp_124_0, temp_124_1)) by {
		lemma_eq_sym(temp_124_1, temp_124_0);
		lemma_mul_assoc(d, a, mul_(c, d));
	}
	let temp_125_0 = (sub_((mul_(a, a)), (mul_(a, a))));
	let temp_125_1 = (mul_((sub_(a, a)), a));
	assert(eq_(temp_125_0, temp_125_1)) by {
		lemma_eq_sym(temp_125_1, temp_125_0);
		lemma_mul_dist(a, a, a);
	}
	let temp_126_0 = (mul_((mul_(c, a)), (add_((mod_(d, m)), c))));
	let temp_126_1 = (mul_((mul_(c, a)), (add_(c, (mod_(d, m))))));
	assert(eq_(temp_126_0, temp_126_1)) by {
		lemma_add_comm(mod_(d, m), c);
		cong_mul_(mul_(c, a), add_(mod_(d, m), c), mul_(c, a), add_(c, mod_(d, m)));
		lemma_eq_ref(mul_(c, a));
	}
	let temp_127_0 = (mul_((mod_((sub_(d, b)), m)), (mod_((mul_(c, d)), m))));
	let temp_127_1 = (mul_((mod_((sub_(d, b)), m)), (mod_((sub_((mul_(c, d)), (mul_((mul_((mul_(b, c)), (mul_(b, a)))), m)))), m))));
	assert(eq_(temp_127_0, temp_127_1)) by {
		lemma_eq_ref(mod_(sub_(d, b), m));
		lemma_mod_mul_vanish(mul_(c, d), mul_(mul_(b, c), mul_(b, a)), m);
		cong_mul_(mod_(sub_(d, b), m), mod_(mul_(c, d), m), mod_(sub_(d, b), m), mod_(sub_(mul_(c, d), mul_(mul_(mul_(b, c), mul_(b, a)), m)), m));
	}
	let temp_128_0 = (mul_((sub_(b, c)), (mul_(d, d))));
	let temp_128_1 = (mul_((sub_(b, c)), (mul_(d, d))));
	assert(eq_(temp_128_0, temp_128_1)) by {
		lemma_eq_ref(temp_128_0);
	}
	let temp_129_0 = (mul_((mul_(a, d)), (mul_(d, b))));
	let temp_129_1 = (mul_((mul_(a, d)), (mul_(b, d))));
	assert(eq_(temp_129_0, temp_129_1)) by {
		cong_mul_(mul_(a, d), mul_(d, b), mul_(a, d), mul_(b, d));
		lemma_mul_comm(d, b);
		lemma_eq_ref(mul_(a, d));
	}
	let temp_130_0 = (mul_((mul_(d, d)), (add_(d, d))));
	let temp_130_1 = (mul_((mul_(d, d)), (add_(d, d))));
	assert(eq_(temp_130_0, temp_130_1)) by {
		lemma_eq_ref(temp_130_0);
	}
	let temp_131_0 = (add_((mul_(a, b)), (sub_((mod_(d, m)), c))));
	let temp_131_1 = (add_((mul_(a, b)), (sub_((mod_((add_((mul_((sub_((mul_(b, a)), (mul_((mod_(c, m)), c)))), m)), d)), m)), c))));
	assert(eq_(temp_131_0, temp_131_1)) by {
		lemma_eq_ref(c);
		lemma_mod_mul_vanish(d, sub_(mul_(b, a), mul_(mod_(c, m), c)), m);
		cong_add_(mul_(a, b), sub_(mod_(d, m), c), mul_(a, b), sub_(mod_(add_(mul_(sub_(mul_(b, a), mul_(mod_(c, m), c)), m), d), m), c));
		lemma_eq_ref(mul_(a, b));
		cong_sub_(mod_(d, m), c, mod_(add_(mul_(sub_(mul_(b, a), mul_(mod_(c, m), c)), m), d), m), c);
	}
	let temp_132_0 = (mod_((mul_((mul_(a, (mod_(c, m)))), (mul_(a, a)))), m));
	let temp_132_1 = (mod_((mul_((mul_((mul_(a, (mod_(c, m)))), a)), a)), m));
	assert(eq_(temp_132_0, temp_132_1)) by {
		lemma_mul_assoc(mul_(a, mod_(c, m)), a, a);
		cong_mod_(mul_(mul_(a, mod_(c, m)), mul_(a, a)), m, mul_(mul_(mul_(a, mod_(c, m)), a), a), m);
		lemma_eq_ref(m);
	}
	let temp_133_0 = (mul_((mul_(d, a)), (mul_(c, b))));
	let temp_133_1 = (mul_(d, (mul_(a, (mul_(c, b))))));
	assert(eq_(temp_133_0, temp_133_1)) by {
		lemma_eq_sym(temp_133_1, temp_133_0);
		lemma_mul_assoc(d, a, mul_(c, b));
	}
	let temp_134_0 = (sub_((mul_(c, c)), (mul_(b, (mod_(d, m))))));
	let temp_134_1 = (sub_((mul_(c, c)), (mul_((mod_(d, m)), b))));
	assert(eq_(temp_134_0, temp_134_1)) by {
		lemma_mul_comm(c, c);
		lemma_mul_comm(b, mod_(d, m));
		cong_sub_(mul_(c, c), mul_(b, mod_(d, m)), mul_(c, c), mul_(mod_(d, m), b));
	}
	let temp_135_0 = (mul_((sub_(b, b)), (mul_(b, d))));
	let temp_135_1 = (mul_((mul_((sub_(b, b)), b)), d));
	assert(eq_(temp_135_0, temp_135_1)) by {
		lemma_mul_assoc(sub_(b, b), b, d);
	}

}

} // verus!