use builtin_macros::*;
// use builtin::*;
mod nl_basics;
use crate::nl_basics::*;
verus! {

pub proof fn free_0(a: Elem, b: Elem, c: Elem, d: Elem, m: Elem)
{
	let temp_0_0 = (mul_((mul_(c, c)), (mul_((mod_(d, m)), a))));
	let temp_0_1 = (mul_((mul_(c, c)), (mul_(a, (mod_(d, m))))));
	assert(eq_(temp_0_0, temp_0_1)) by {
		lemma_mul_comm(c, c);
		lemma_mul_comm(mod_(d, m), a);
		cong_mul_(mul_(c, c), mul_(mod_(d, m), a), mul_(c, c), mul_(a, mod_(d, m)));
	}
	let temp_1_0 = (mul_((mul_(b, c)), (mul_(as_elem(57), c))));
	let temp_1_1 = (mul_((mul_((mul_(b, c)), as_elem(57))), c));
	assert(eq_(temp_1_0, temp_1_1)) by {
		lemma_mul_assoc(mul_(b, c), as_elem(57), c);
	}
	let temp_2_0 = (mul_((mul_((mod_(c, m)), d)), (mul_(b, b))));
	let temp_2_1 = (mul_((mul_((mul_((mod_(c, m)), d)), b)), b));
	assert(eq_(temp_2_0, temp_2_1)) by {
		lemma_mul_assoc(mul_(mod_(c, m), d), b, b);
	}
	let temp_3_0 = (mul_((mod_((mul_(a, a)), m)), (mul_(c, a))));
	let temp_3_1 = (mul_((mod_((add_((mul_((mul_((mul_(b, c)), (sub_(a, b)))), m)), (mul_(a, a)))), m)), (mul_(c, a))));
	assert(eq_(temp_3_0, temp_3_1)) by {
		lemma_mod_mul_vanish(mul_(a, a), mul_(mul_(b, c), sub_(a, b)), m);
		cong_mul_(mod_(mul_(a, a), m), mul_(c, a), mod_(add_(mul_(mul_(mul_(b, c), sub_(a, b)), m), mul_(a, a)), m), mul_(c, a));
		lemma_eq_ref(mul_(c, a));
	}
	let temp_4_0 = (mul_((mod_((mul_(d, b)), m)), (mul_(d, b))));
	let temp_4_1 = (mul_((mul_(d, b)), (mod_((mul_(d, b)), m))));
	assert(eq_(temp_4_0, temp_4_1)) by {
		lemma_mul_comm(mod_(mul_(d, b), m), mul_(d, b));
	}
	let temp_5_0 = (mul_((mul_(d, (mod_(a, m)))), (mul_(c, d))));
	let temp_5_1 = (mul_((mul_((mul_(d, (mod_(a, m)))), c)), d));
	assert(eq_(temp_5_0, temp_5_1)) by {
		lemma_mul_assoc(mul_(d, mod_(a, m)), c, d);
	}
	let temp_6_0 = (mul_((mul_(c, a)), (sub_(d, a))));
	let temp_6_1 = (mul_((sub_(d, a)), (mul_(c, a))));
	assert(eq_(temp_6_0, temp_6_1)) by {
		lemma_mul_comm(mul_(c, a), sub_(d, a));
	}
	let temp_7_0 = (mul_((mul_((mod_(d, m)), a)), (mul_(d, d))));
	let temp_7_1 = (mul_((mul_((mod_((add_(d, (mul_((mul_((mul_(b, b)), (sub_(b, a)))), m)))), m)), a)), (mul_(d, d))));
	assert(eq_(temp_7_0, temp_7_1)) by {
		lemma_mul_comm(d, d);
		lemma_mod_mul_vanish(d, mul_(mul_(b, b), sub_(b, a)), m);
		cong_mul_(mul_(mod_(d, m), a), mul_(d, d), mul_(mod_(add_(d, mul_(mul_(mul_(b, b), sub_(b, a)), m)), m), a), mul_(d, d));
		cong_mul_(mod_(d, m), a, mod_(add_(d, mul_(mul_(mul_(b, b), sub_(b, a)), m)), m), a);
		lemma_eq_ref(a);
	}
	let temp_8_0 = (mul_((mul_(b, b)), (mod_((mul_(b, c)), m))));
	let temp_8_1 = (mul_((mul_(b, b)), (mod_((sub_((mul_(b, c)), (mul_((mul_((mod_((sub_((mod_(c, m)), b)), m)), (mul_(a, a)))), m)))), m))));
	assert(eq_(temp_8_0, temp_8_1)) by {
		lemma_mul_comm(b, b);
		lemma_mod_mul_vanish(mul_(b, c), mul_(mod_(sub_(mod_(c, m), b), m), mul_(a, a)), m);
		cong_mul_(mul_(b, b), mod_(mul_(b, c), m), mul_(b, b), mod_(sub_(mul_(b, c), mul_(mul_(mod_(sub_(mod_(c, m), b), m), mul_(a, a)), m)), m));
	}
	let temp_9_0 = (mul_((mul_(d, c)), (mul_(d, c))));
	let temp_9_1 = (mul_((mul_(d, c)), (mul_(d, c))));
	assert(eq_(temp_9_0, temp_9_1)) by {
		lemma_eq_ref(temp_9_0);
	}
	let temp_10_0 = (sub_((mul_(c, b)), (mod_((mul_(a, c)), m))));
	let temp_10_1 = (sub_((mul_(c, b)), (mod_((mul_(c, a)), m))));
	assert(eq_(temp_10_0, temp_10_1)) by {
		lemma_mul_comm(a, c);
		cong_sub_(mul_(c, b), mod_(mul_(a, c), m), mul_(c, b), mod_(mul_(c, a), m));
		lemma_eq_ref(mul_(c, b));
		cong_mod_(mul_(a, c), m, mul_(c, a), m);
		lemma_eq_ref(m);
	}
	let temp_11_0 = (mul_((mul_(a, a)), (mul_(b, a))));
	let temp_11_1 = (mul_(a, (mul_(a, (mul_(b, a))))));
	assert(eq_(temp_11_0, temp_11_1)) by {
		lemma_eq_sym(temp_11_1, temp_11_0);
		lemma_mul_assoc(a, a, mul_(b, a));
	}
	let temp_12_0 = (mul_((mul_(b, c)), (mul_(c, (mod_(b, m))))));
	let temp_12_1 = (mul_((mul_((mul_(b, c)), c)), (mod_(b, m))));
	assert(eq_(temp_12_0, temp_12_1)) by {
		lemma_mul_assoc(mul_(b, c), c, mod_(b, m));
	}
	let temp_13_0 = (add_((sub_(d, (mod_(b, m)))), (mul_(a, (mod_(a, m))))));
	let temp_13_1 = (add_((sub_(d, (mod_((add_(b, (mul_((mul_((mul_((mod_(a, m)), a)), (mul_(d, a)))), m)))), m)))), (mul_(a, (mod_(a, m))))));
	assert(eq_(temp_13_0, temp_13_1)) by {
		lemma_mod_mul_vanish(b, mul_(mul_(mod_(a, m), a), mul_(d, a)), m);
		cong_add_(sub_(d, mod_(b, m)), mul_(a, mod_(a, m)), sub_(d, mod_(add_(b, mul_(mul_(mul_(mod_(a, m), a), mul_(d, a)), m)), m)), mul_(a, mod_(a, m)));
		cong_sub_(d, mod_(b, m), d, mod_(add_(b, mul_(mul_(mul_(mod_(a, m), a), mul_(d, a)), m)), m));
		lemma_eq_ref(mul_(a, mod_(a, m)));
		lemma_eq_ref(d);
	}
	let temp_14_0 = (mul_((mul_(a, b)), (add_(b, a))));
	let temp_14_1 = (mul_(a, (mul_(b, (add_(b, a))))));
	assert(eq_(temp_14_0, temp_14_1)) by {
		lemma_eq_sym(temp_14_1, temp_14_0);
		lemma_mul_assoc(a, b, add_(b, a));
	}
	let temp_15_0 = (sub_((mul_(d, b)), (mul_(b, d))));
	let temp_15_1 = (sub_((mul_(b, d)), (mul_(b, d))));
	assert(eq_(temp_15_0, temp_15_1)) by {
		cong_sub_(mul_(d, b), mul_(b, d), mul_(b, d), mul_(b, d));
		lemma_mul_comm(d, b);
		lemma_eq_ref(mul_(b, d));
	}
	let temp_16_0 = (mod_((add_((add_(c, (mod_(c, m)))), (mul_(d, c)))), m));
	let temp_16_1 = (mod_((add_((mod_((add_(c, (mod_(c, m)))), m)), (mul_(d, c)))), m));
	assert(eq_(temp_16_0, temp_16_1)) by {
		lemma_mod_add_noop(add_(c, mod_(c, m)), mul_(d, c), m);
	}
	let temp_17_0 = (mul_((mul_(c, as_elem(6))), (mod_((mul_(b, b)), m))));
	let temp_17_1 = (mul_((mul_(as_elem(6), c)), (mod_((mul_(b, b)), m))));
	assert(eq_(temp_17_0, temp_17_1)) by {
		lemma_mul_comm(c, as_elem(6));
		cong_mul_(mul_(c, as_elem(6)), mod_(mul_(b, b), m), mul_(as_elem(6), c), mod_(mul_(b, b), m));
		lemma_eq_ref(mod_(mul_(b, b), m));
	}
	let temp_18_0 = (mul_((sub_(as_elem(6), c)), (mul_(a, d))));
	let temp_18_1 = (mul_((mul_((sub_(as_elem(6), c)), a)), d));
	assert(eq_(temp_18_0, temp_18_1)) by {
		lemma_mul_assoc(sub_(as_elem(6), c), a, d);
	}
	let temp_19_0 = (add_((sub_(a, (mod_(c, m)))), (add_(d, a))));
	let temp_19_1 = (add_((sub_(a, (mod_((sub_(c, (mul_((mul_((mul_(b, b)), (mul_(a, b)))), m)))), m)))), (add_(d, a))));
	assert(eq_(temp_19_0, temp_19_1)) by {
		cong_sub_(a, mod_(c, m), a, mod_(sub_(c, mul_(mul_(mul_(b, b), mul_(a, b)), m)), m));
		lemma_eq_ref(a);
		lemma_mod_mul_vanish(c, mul_(mul_(b, b), mul_(a, b)), m);
		cong_add_(sub_(a, mod_(c, m)), add_(d, a), sub_(a, mod_(sub_(c, mul_(mul_(mul_(b, b), mul_(a, b)), m)), m)), add_(d, a));
		lemma_eq_ref(add_(d, a));
	}
	let temp_20_0 = (mul_((mul_(c, c)), (mul_(b, a))));
	let temp_20_1 = (mul_(c, (mul_(c, (mul_(b, a))))));
	assert(eq_(temp_20_0, temp_20_1)) by {
		lemma_eq_sym(temp_20_1, temp_20_0);
		lemma_mul_assoc(c, c, mul_(b, a));
	}
	let temp_21_0 = (mul_((sub_(a, b)), (mul_(d, d))));
	let temp_21_1 = (mul_((mul_(d, d)), (sub_(a, b))));
	assert(eq_(temp_21_0, temp_21_1)) by {
		lemma_mul_comm(sub_(a, b), mul_(d, d));
	}
	let temp_22_0 = (mod_((mul_((add_(a, a)), (mul_(a, d)))), m));
	let temp_22_1 = (mod_((mul_((mul_(a, d)), (add_(a, a)))), m));
	assert(eq_(temp_22_0, temp_22_1)) by {
		cong_mod_(mul_(add_(a, a), mul_(a, d)), m, mul_(mul_(a, d), add_(a, a)), m);
		lemma_mul_comm(add_(a, a), mul_(a, d));
		lemma_eq_ref(m);
	}
	let temp_23_0 = (mul_((mul_((mod_(b, m)), (mod_(a, m)))), (mul_(b, b))));
	let temp_23_1 = (mul_((mod_(b, m)), (mul_((mod_(a, m)), (mul_(b, b))))));
	assert(eq_(temp_23_0, temp_23_1)) by {
		lemma_mul_assoc(mod_(b, m), mod_(a, m), mul_(b, b));
		lemma_eq_sym(temp_23_1, temp_23_0);
	}
	let temp_24_0 = (mul_((mul_(a, c)), (mul_(a, (mod_(b, m))))));
	let temp_24_1 = (mul_(a, (mul_(c, (mul_(a, (mod_(b, m))))))));
	assert(eq_(temp_24_0, temp_24_1)) by {
		lemma_mul_assoc(a, c, mul_(a, mod_(b, m)));
		lemma_eq_sym(temp_24_1, temp_24_0);
	}
	let temp_25_0 = (mod_((mul_((mul_(c, c)), (mul_((mod_(c, m)), c)))), m));
	let temp_25_1 = (mod_((mul_((mul_(c, c)), (mul_(c, (mod_(c, m)))))), m));
	assert(eq_(temp_25_0, temp_25_1)) by {
		lemma_mul_comm(c, c);
		lemma_mul_comm(mod_(c, m), c);
		cong_mod_(mul_(mul_(c, c), mul_(mod_(c, m), c)), m, mul_(mul_(c, c), mul_(c, mod_(c, m))), m);
		cong_mul_(mul_(c, c), mul_(mod_(c, m), c), mul_(c, c), mul_(c, mod_(c, m)));
		lemma_eq_ref(m);
	}
	let temp_26_0 = (mod_((mul_((mul_(c, c)), (mul_(d, a)))), m));
	let temp_26_1 = (mod_((add_((mul_((mul_(c, c)), (mul_(d, a)))), (mul_((mul_((mul_(a, c)), (mod_((mul_((mod_(a, m)), d)), m)))), m)))), m));
	assert(eq_(temp_26_0, temp_26_1)) by {
		lemma_mod_mul_vanish(mul_(mul_(c, c), mul_(d, a)), mul_(mul_(a, c), mod_(mul_(mod_(a, m), d), m)), m);
	}
	let temp_27_0 = (mul_((mul_((mod_(c, m)), (mod_(a, m)))), (mul_(b, c))));
	let temp_27_1 = (mul_((mul_((mod_((add_(c, (mul_((mul_((mod_((mul_(a, b)), m)), (mul_(c, c)))), m)))), m)), (mod_(a, m)))), (mul_(b, c))));
	assert(eq_(temp_27_0, temp_27_1)) by {
		lemma_mod_mul_vanish(c, mul_(mod_(mul_(a, b), m), mul_(c, c)), m);
		cong_mul_(mul_(mod_(c, m), mod_(a, m)), mul_(b, c), mul_(mod_(add_(c, mul_(mul_(mod_(mul_(a, b), m), mul_(c, c)), m)), m), mod_(a, m)), mul_(b, c));
		lemma_eq_ref(mod_(a, m));
		cong_mul_(mod_(c, m), mod_(a, m), mod_(add_(c, mul_(mul_(mod_(mul_(a, b), m), mul_(c, c)), m)), m), mod_(a, m));
		lemma_eq_ref(mul_(b, c));
	}
	let temp_28_0 = (sub_((mul_(b, d)), b));
	let temp_28_1 = (sub_((mul_(d, b)), b));
	assert(eq_(temp_28_0, temp_28_1)) by {
		cong_sub_(mul_(b, d), b, mul_(d, b), b);
		lemma_mul_comm(b, d);
		lemma_eq_ref(b);
	}
	let temp_29_0 = (mul_((mul_((mod_(b, m)), d)), (mul_(a, a))));
	let temp_29_1 = (mul_((mul_(d, (mod_(b, m)))), (mul_(a, a))));
	assert(eq_(temp_29_0, temp_29_1)) by {
		lemma_mul_comm(mod_(b, m), d);
		lemma_mul_comm(a, a);
		cong_mul_(mul_(mod_(b, m), d), mul_(a, a), mul_(d, mod_(b, m)), mul_(a, a));
	}
	let temp_30_0 = (mul_((mul_(d, b)), (add_(d, (mod_(a, m))))));
	let temp_30_1 = (mul_((mul_(d, b)), (add_(d, (mod_((add_(a, (mul_((mul_((mul_(c, a)), (add_(d, d)))), m)))), m))))));
	assert(eq_(temp_30_0, temp_30_1)) by {
		lemma_mod_mul_vanish(a, mul_(mul_(c, a), add_(d, d)), m);
		cong_mul_(mul_(d, b), add_(d, mod_(a, m)), mul_(d, b), add_(d, mod_(add_(a, mul_(mul_(mul_(c, a), add_(d, d)), m)), m)));
		lemma_eq_ref(mul_(d, b));
		lemma_eq_ref(d);
		cong_add_(d, mod_(a, m), d, mod_(add_(a, mul_(mul_(mul_(c, a), add_(d, d)), m)), m));
	}
	let temp_31_0 = (mul_((mul_(c, c)), (mul_(c, b))));
	let temp_31_1 = (mul_(c, (mul_(c, (mul_(c, b))))));
	assert(eq_(temp_31_0, temp_31_1)) by {
		lemma_eq_sym(temp_31_1, temp_31_0);
		lemma_mul_assoc(c, c, mul_(c, b));
	}
	let temp_32_0 = (mod_((mul_((mul_(d, b)), (sub_(c, d)))), m));
	let temp_32_1 = (mod_((add_((mul_((sub_((mul_(c, c)), (mul_(d, a)))), m)), (mul_((mul_(d, b)), (sub_(c, d)))))), m));
	assert(eq_(temp_32_0, temp_32_1)) by {
		lemma_mod_mul_vanish(mul_(mul_(d, b), sub_(c, d)), sub_(mul_(c, c), mul_(d, a)), m);
	}
	let temp_33_0 = (mul_((mul_(b, b)), (mul_(a, d))));
	let temp_33_1 = (mul_((mul_(a, d)), (mul_(b, b))));
	assert(eq_(temp_33_0, temp_33_1)) by {
		lemma_mul_comm(mul_(b, b), mul_(a, d));
	}
	let temp_34_0 = (add_((sub_(c, a)), (mul_(b, d))));
	let temp_34_1 = (add_((sub_(c, a)), (mul_(d, b))));
	assert(eq_(temp_34_0, temp_34_1)) by {
		cong_add_(sub_(c, a), mul_(b, d), sub_(c, a), mul_(d, b));
		lemma_mul_comm(b, d);
		lemma_eq_ref(sub_(c, a));
	}
	let temp_35_0 = (mul_((mul_(a, b)), (mul_(a, (mod_(d, m))))));
	let temp_35_1 = (mul_((mul_(a, b)), (mul_((mod_(d, m)), a))));
	assert(eq_(temp_35_0, temp_35_1)) by {
		lemma_mul_comm(mod_(d, m), a);
		cong_mul_(mul_(a, b), mul_(a, mod_(d, m)), mul_(a, b), mul_(mod_(d, m), a));
		lemma_eq_sym(mul_(mod_(d, m), a), mul_(a, mod_(d, m)));
		lemma_eq_ref(mul_(a, b));
	}
	let temp_36_0 = (sub_((mod_((mul_(a, a)), m)), (mul_(b, c))));
	let temp_36_1 = (sub_((mod_((mul_(a, a)), m)), (mul_(b, c))));
	assert(eq_(temp_36_0, temp_36_1)) by {
		lemma_eq_ref(temp_36_0);
	}
	let temp_37_0 = (mul_((sub_(d, b)), (mul_(b, c))));
	let temp_37_1 = (sub_((mul_(d, (mul_(b, c)))), (mul_(b, (mul_(b, c))))));
	assert(eq_(temp_37_0, temp_37_1)) by {
		lemma_mul_dist(mul_(b, c), d, b);
	}
	let temp_38_0 = (mod_((mul_((sub_(a, (mod_(d, m)))), (add_(d, (mod_(c, m)))))), m));
	let temp_38_1 = (mod_((mul_((sub_(a, (mod_(d, m)))), (add_((mod_(c, m)), d)))), m));
	assert(eq_(temp_38_0, temp_38_1)) by {
		lemma_add_comm(d, mod_(c, m));
		cong_mod_(mul_(sub_(a, mod_(d, m)), add_(d, mod_(c, m))), m, mul_(sub_(a, mod_(d, m)), add_(mod_(c, m), d)), m);
		lemma_eq_ref(sub_(a, mod_(d, m)));
		cong_mul_(sub_(a, mod_(d, m)), add_(d, mod_(c, m)), sub_(a, mod_(d, m)), add_(mod_(c, m), d));
		lemma_eq_ref(m);
	}
	let temp_39_0 = (add_((mul_(a, (mod_(c, m)))), (mul_(a, b))));
	let temp_39_1 = (mul_(a, (add_((mod_(c, m)), b))));
	assert(eq_(temp_39_0, temp_39_1)) by {
		lemma_mul_dist(a, mod_(c, m), b);
		lemma_eq_sym(temp_39_1, temp_39_0);
	}
	let temp_40_0 = (mul_((mul_((mod_(c, m)), b)), (mul_(c, b))));
	let temp_40_1 = (mul_((mul_((mod_((add_(c, (mul_((mul_((sub_(d, c)), (mul_(c, c)))), m)))), m)), b)), (mul_(c, b))));
	assert(eq_(temp_40_0, temp_40_1)) by {
		lemma_mod_mul_vanish(c, mul_(sub_(d, c), mul_(c, c)), m);
		cong_mul_(mul_(mod_(c, m), b), mul_(c, b), mul_(mod_(add_(c, mul_(mul_(sub_(d, c), mul_(c, c)), m)), m), b), mul_(c, b));
		lemma_eq_ref(b);
		cong_mul_(mod_(c, m), b, mod_(add_(c, mul_(mul_(sub_(d, c), mul_(c, c)), m)), m), b);
		lemma_eq_ref(mul_(c, b));
	}
	let temp_41_0 = (mul_((mul_(a, a)), (mul_(d, a))));
	let temp_41_1 = (mul_((mul_(a, a)), (mul_(a, d))));
	assert(eq_(temp_41_0, temp_41_1)) by {
		cong_mul_(mul_(a, a), mul_(d, a), mul_(a, a), mul_(a, d));
		lemma_mul_comm(a, a);
		lemma_mul_comm(d, a);
	}
	let temp_42_0 = (mod_((mul_((add_(d, d)), (add_((mod_(a, m)), c)))), m));
	let temp_42_1 = (mod_((add_((mul_(d, (add_((mod_(a, m)), c)))), (mul_(d, (add_((mod_(a, m)), c)))))), m));
	assert(eq_(temp_42_0, temp_42_1)) by {
		lemma_mul_dist(d, d, add_(mod_(a, m), c));
		cong_mod_(mul_(add_(d, d), add_(mod_(a, m), c)), m, add_(mul_(d, add_(mod_(a, m), c)), mul_(d, add_(mod_(a, m), c))), m);
		lemma_eq_ref(m);
	}
	let temp_43_0 = (mul_((mul_(a, a)), (mul_(d, d))));
	let temp_43_1 = (mul_((mul_((mul_(a, a)), d)), d));
	assert(eq_(temp_43_0, temp_43_1)) by {
		lemma_mul_assoc(mul_(a, a), d, d);
	}
	let temp_44_0 = (mul_((mul_((mod_(a, m)), d)), (mul_(c, d))));
	let temp_44_1 = (mul_((mul_((mod_((add_(a, (mul_((mul_((mul_(c, a)), (mul_(d, (mod_(c, m)))))), m)))), m)), d)), (mul_(c, d))));
	assert(eq_(temp_44_0, temp_44_1)) by {
		lemma_mod_mul_vanish(a, mul_(mul_(c, a), mul_(d, mod_(c, m))), m);
		cong_mul_(mul_(mod_(a, m), d), mul_(c, d), mul_(mod_(add_(a, mul_(mul_(mul_(c, a), mul_(d, mod_(c, m))), m)), m), d), mul_(c, d));
		lemma_eq_ref(d);
		cong_mul_(mod_(a, m), d, mod_(add_(a, mul_(mul_(mul_(c, a), mul_(d, mod_(c, m))), m)), m), d);
		lemma_eq_ref(mul_(c, d));
	}
	let temp_45_0 = (sub_((sub_(b, a)), (mul_(a, c))));
	let temp_45_1 = (sub_((sub_(b, a)), (mul_(c, a))));
	assert(eq_(temp_45_0, temp_45_1)) by {
		cong_sub_(sub_(b, a), mul_(a, c), sub_(b, a), mul_(c, a));
		lemma_mul_comm(a, c);
		lemma_eq_ref(sub_(b, a));
	}
	let temp_46_0 = (add_((sub_(c, c)), (mul_(a, c))));
	let temp_46_1 = (add_((sub_(c, c)), (mul_(c, a))));
	assert(eq_(temp_46_0, temp_46_1)) by {
		lemma_eq_ref(sub_(c, c));
		cong_add_(sub_(c, c), mul_(a, c), sub_(c, c), mul_(c, a));
		lemma_mul_comm(a, c);
	}
	let temp_47_0 = (sub_((mul_(c, a)), (mul_((mod_(d, m)), a))));
	let temp_47_1 = (sub_((mul_(c, a)), (mul_((mod_((sub_(d, (mul_((mod_((mul_((mul_(b, a)), (mod_((mul_(d, d)), m)))), m)), m)))), m)), a))));
	assert(eq_(temp_47_0, temp_47_1)) by {
		cong_sub_(mul_(c, a), mul_(mod_(d, m), a), mul_(c, a), mul_(mod_(sub_(d, mul_(mod_(mul_(mul_(b, a), mod_(mul_(d, d), m)), m), m)), m), a));
		lemma_mod_mul_vanish(d, mod_(mul_(mul_(b, a), mod_(mul_(d, d), m)), m), m);
		lemma_eq_ref(a);
		lemma_eq_ref(mul_(c, a));
		cong_mul_(mod_(d, m), a, mod_(sub_(d, mul_(mod_(mul_(mul_(b, a), mod_(mul_(d, d), m)), m), m)), m), a);
	}
	let temp_48_0 = (mul_((mul_(d, c)), (mul_(c, as_elem(53)))));
	let temp_48_1 = (mul_((mul_((mul_(d, c)), c)), as_elem(53)));
	assert(eq_(temp_48_0, temp_48_1)) by {
		lemma_mul_assoc(mul_(d, c), c, as_elem(53));
	}
	let temp_49_0 = (mul_((mod_((mul_(a, (mod_(b, m)))), m)), (mul_((mod_(a, m)), (mod_(d, m))))));
	let temp_49_1 = (mul_((mul_((mod_((mul_(a, (mod_(b, m)))), m)), (mod_(a, m)))), (mod_(d, m))));
	assert(eq_(temp_49_0, temp_49_1)) by {
		lemma_mul_assoc(mod_(mul_(a, mod_(b, m)), m), mod_(a, m), mod_(d, m));
	}
	let temp_50_0 = (mul_((mul_(b, c)), (mul_(a, b))));
	let temp_50_1 = (mul_(b, (mul_(c, (mul_(a, b))))));
	assert(eq_(temp_50_0, temp_50_1)) by {
		lemma_eq_sym(temp_50_1, temp_50_0);
		lemma_mul_assoc(b, c, mul_(a, b));
	}
	let temp_51_0 = (mod_((mul_((mul_(as_elem(94), c)), (mul_(b, d)))), m));
	let temp_51_1 = (mod_((mul_((mul_(as_elem(94), c)), (mul_(d, b)))), m));
	assert(eq_(temp_51_0, temp_51_1)) by {
		lemma_mul_comm(b, d);
		cong_mod_(mul_(mul_(as_elem(94), c), mul_(b, d)), m, mul_(mul_(as_elem(94), c), mul_(d, b)), m);
		lemma_eq_ref(mul_(as_elem(94), c));
		cong_mul_(mul_(as_elem(94), c), mul_(b, d), mul_(as_elem(94), c), mul_(d, b));
		lemma_eq_ref(m);
	}
	let temp_52_0 = (mul_((mul_(b, b)), (add_(c, a))));
	let temp_52_1 = (mul_(b, (mul_(b, (add_(c, a))))));
	assert(eq_(temp_52_0, temp_52_1)) by {
		lemma_eq_sym(temp_52_1, temp_52_0);
		lemma_mul_assoc(b, b, add_(c, a));
	}
	let temp_53_0 = (mul_((mul_(a, a)), (mod_((mul_(as_elem(18), d)), m))));
	let temp_53_1 = (mul_(a, (mul_(a, (mod_((mul_(as_elem(18), d)), m))))));
	assert(eq_(temp_53_0, temp_53_1)) by {
		lemma_mul_assoc(a, a, mod_(mul_(as_elem(18), d), m));
		lemma_eq_sym(temp_53_1, temp_53_0);
	}
	let temp_54_0 = (mul_((mul_(a, b)), (mul_(a, b))));
	let temp_54_1 = (mul_((mul_(a, b)), (mul_(b, a))));
	assert(eq_(temp_54_0, temp_54_1)) by {
		cong_mul_(mul_(a, b), mul_(a, b), mul_(a, b), mul_(b, a));
		lemma_mul_comm(a, b);
		lemma_eq_ref(mul_(a, b));
	}
	let temp_55_0 = (mul_((mul_(d, b)), (mod_((mul_(d, (mod_(d, m)))), m))));
	let temp_55_1 = (mul_((mul_(d, b)), (mod_((mul_(d, (mod_((add_(d, (mul_((mul_((sub_(c, c)), (mul_(b, b)))), m)))), m)))), m))));
	assert(eq_(temp_55_0, temp_55_1)) by {
		lemma_mod_mul_vanish(d, mul_(sub_(c, c), mul_(b, b)), m);
		cong_mul_(mul_(d, b), mod_(mul_(d, mod_(d, m)), m), mul_(d, b), mod_(mul_(d, mod_(add_(d, mul_(mul_(sub_(c, c), mul_(b, b)), m)), m)), m));
		cong_mod_(mul_(d, mod_(d, m)), m, mul_(d, mod_(add_(d, mul_(mul_(sub_(c, c), mul_(b, b)), m)), m)), m);
		lemma_eq_ref(mul_(d, b));
		lemma_eq_ref(d);
		cong_mul_(d, mod_(d, m), d, mod_(add_(d, mul_(mul_(sub_(c, c), mul_(b, b)), m)), m));
		lemma_eq_ref(m);
	}
	let temp_56_0 = (mod_((mul_((mul_(b, c)), (mul_(d, d)))), m));
	let temp_56_1 = (mod_((mul_((mul_(b, c)), (mul_(d, d)))), m));
	assert(eq_(temp_56_0, temp_56_1)) by {
		lemma_eq_ref(temp_56_0);
	}
	let temp_57_0 = (mul_((mul_(b, b)), (mul_(b, b))));
	let temp_57_1 = (mul_((mul_(b, b)), (mul_(b, b))));
	assert(eq_(temp_57_0, temp_57_1)) by {
		lemma_eq_ref(temp_57_0);
	}
	let temp_58_0 = (mul_((mul_(b, b)), (mul_((mod_(c, m)), c))));
	let temp_58_1 = (mul_((mul_(b, b)), (mul_(c, (mod_(c, m))))));
	assert(eq_(temp_58_0, temp_58_1)) by {
		cong_mul_(mul_(b, b), mul_(mod_(c, m), c), mul_(b, b), mul_(c, mod_(c, m)));
		lemma_mul_comm(b, b);
		lemma_mul_comm(mod_(c, m), c);
	}
	let temp_59_0 = (mul_((mul_(a, b)), (sub_(b, d))));
	let temp_59_1 = (mul_(a, (mul_(b, (sub_(b, d))))));
	assert(eq_(temp_59_0, temp_59_1)) by {
		lemma_eq_sym(temp_59_1, temp_59_0);
		lemma_mul_assoc(a, b, sub_(b, d));
	}
	let temp_60_0 = (mul_((mul_(b, b)), (mul_(c, d))));
	let temp_60_1 = (mul_((mul_(b, b)), (mul_(d, c))));
	assert(eq_(temp_60_0, temp_60_1)) by {
		cong_mul_(mul_(b, b), mul_(c, d), mul_(b, b), mul_(d, c));
		lemma_mul_comm(b, b);
		lemma_mul_comm(c, d);
	}
	let temp_61_0 = (sub_((mul_(d, a)), (add_(c, (mod_(d, m))))));
	let temp_61_1 = (sub_((mul_(a, d)), (add_(c, (mod_(d, m))))));
	assert(eq_(temp_61_0, temp_61_1)) by {
		lemma_mul_comm(d, a);
		cong_sub_(mul_(d, a), add_(c, mod_(d, m)), mul_(a, d), add_(c, mod_(d, m)));
		lemma_eq_ref(add_(c, mod_(d, m)));
	}
	let temp_62_0 = (mod_((mul_((mul_(b, (mod_(b, m)))), (sub_(a, (mod_(a, m)))))), m));
	let temp_62_1 = (mod_((mul_((mul_(b, (mod_(b, m)))), (sub_(a, (mod_((add_(a, (mul_((mul_((mul_(c, d)), (mul_(d, d)))), m)))), m)))))), m));
	assert(eq_(temp_62_0, temp_62_1)) by {
		lemma_eq_ref(a);
		lemma_mod_mul_vanish(a, mul_(mul_(c, d), mul_(d, d)), m);
		cong_mod_(mul_(mul_(b, mod_(b, m)), sub_(a, mod_(a, m))), m, mul_(mul_(b, mod_(b, m)), sub_(a, mod_(add_(a, mul_(mul_(mul_(c, d), mul_(d, d)), m)), m))), m);
		lemma_eq_ref(mul_(b, mod_(b, m)));
		cong_mul_(mul_(b, mod_(b, m)), sub_(a, mod_(a, m)), mul_(b, mod_(b, m)), sub_(a, mod_(add_(a, mul_(mul_(mul_(c, d), mul_(d, d)), m)), m)));
		cong_sub_(a, mod_(a, m), a, mod_(add_(a, mul_(mul_(mul_(c, d), mul_(d, d)), m)), m));
		lemma_eq_ref(m);
	}
	let temp_63_0 = (add_((mul_(b, a)), (add_(b, b))));
	let temp_63_1 = (add_((add_(b, b)), (mul_(b, a))));
	assert(eq_(temp_63_0, temp_63_1)) by {
		lemma_add_comm(mul_(b, a), add_(b, b));
	}
	let temp_64_0 = (mul_((mul_(d, a)), (mod_((add_(b, c)), m))));
	let temp_64_1 = (mul_(d, (mul_(a, (mod_((add_(b, c)), m))))));
	assert(eq_(temp_64_0, temp_64_1)) by {
		lemma_mul_assoc(d, a, mod_(add_(b, c), m));
		lemma_eq_sym(temp_64_1, temp_64_0);
	}
	let temp_65_0 = (mul_((mul_(d, d)), (mul_(c, a))));
	let temp_65_1 = (mul_((mul_((mul_(d, d)), c)), a));
	assert(eq_(temp_65_0, temp_65_1)) by {
		lemma_mul_assoc(mul_(d, d), c, a);
	}
	let temp_66_0 = (mul_((mul_(as_elem(12), a)), (mul_(as_elem(49), c))));
	let temp_66_1 = (mul_(as_elem(12), (mul_(a, (mul_(as_elem(49), c))))));
	assert(eq_(temp_66_0, temp_66_1)) by {
		lemma_mul_assoc(as_elem(12), a, mul_(as_elem(49), c));
		lemma_eq_sym(temp_66_1, temp_66_0);
	}
	let temp_67_0 = (mod_((mul_((add_(a, a)), (mul_(c, c)))), m));
	let temp_67_1 = (mod_((mul_((add_(a, a)), (mul_(c, c)))), m));
	assert(eq_(temp_67_0, temp_67_1)) by {
		lemma_eq_ref(temp_67_0);
	}
	let temp_68_0 = (add_((mul_(b, d)), (mul_(a, (mod_(a, m))))));
	let temp_68_1 = (add_((mul_(b, d)), (mul_((mod_(a, m)), a))));
	assert(eq_(temp_68_0, temp_68_1)) by {
		lemma_mul_comm(a, mod_(a, m));
		cong_add_(mul_(b, d), mul_(a, mod_(a, m)), mul_(b, d), mul_(mod_(a, m), a));
		lemma_eq_ref(mul_(b, d));
	}
	let temp_69_0 = (mul_((add_(d, c)), (mul_(b, b))));
	let temp_69_1 = (mul_((add_(c, d)), (mul_(b, b))));
	assert(eq_(temp_69_0, temp_69_1)) by {
		cong_mul_(add_(d, c), mul_(b, b), add_(c, d), mul_(b, b));
		lemma_add_comm(d, c);
		lemma_mul_comm(b, b);
	}
	let temp_70_0 = (mul_((sub_(a, d)), a));
	let temp_70_1 = (sub_((mul_(a, a)), (mul_(d, a))));
	assert(eq_(temp_70_0, temp_70_1)) by {
		lemma_mul_dist(a, a, d);
	}
	let temp_71_0 = (mul_((sub_(a, b)), (sub_(b, b))));
	let temp_71_1 = (mul_((sub_(b, b)), (sub_(a, b))));
	assert(eq_(temp_71_0, temp_71_1)) by {
		lemma_mul_comm(sub_(a, b), sub_(b, b));
	}
	let temp_72_0 = (mul_((mul_(a, a)), (mul_(b, b))));
	let temp_72_1 = (mul_((mul_(a, a)), (mul_(b, b))));
	assert(eq_(temp_72_0, temp_72_1)) by {
		lemma_eq_ref(temp_72_0);
	}
	let temp_73_0 = (mod_((mul_((sub_(c, a)), (mul_(b, d)))), m));
	let temp_73_1 = (mod_((mul_((sub_(c, a)), (mul_(d, b)))), m));
	assert(eq_(temp_73_0, temp_73_1)) by {
		lemma_mul_comm(b, d);
		cong_mod_(mul_(sub_(c, a), mul_(b, d)), m, mul_(sub_(c, a), mul_(d, b)), m);
		lemma_eq_ref(sub_(c, a));
		cong_mul_(sub_(c, a), mul_(b, d), sub_(c, a), mul_(d, b));
		lemma_eq_ref(m);
	}
	let temp_74_0 = (mul_((mul_(a, c)), (mul_(a, c))));
	let temp_74_1 = (mul_((mul_((mul_(a, c)), a)), c));
	assert(eq_(temp_74_0, temp_74_1)) by {
		lemma_mul_assoc(mul_(a, c), a, c);
	}
	let temp_75_0 = (mul_((add_(b, d)), (mul_(c, c))));
	let temp_75_1 = (add_((mul_(b, (mul_(c, c)))), (mul_(d, (mul_(c, c))))));
	assert(eq_(temp_75_0, temp_75_1)) by {
		lemma_mul_dist(b, d, mul_(c, c));
	}
	let temp_76_0 = (mul_((mul_(d, d)), (add_(d, c))));
	let temp_76_1 = (mul_((mul_(d, d)), (add_(d, c))));
	assert(eq_(temp_76_0, temp_76_1)) by {
		lemma_eq_ref(temp_76_0);
	}
	let temp_77_0 = (add_((mul_(b, d)), (mul_(a, a))));
	let temp_77_1 = (add_((mul_(d, b)), (mul_(a, a))));
	assert(eq_(temp_77_0, temp_77_1)) by {
		cong_add_(mul_(b, d), mul_(a, a), mul_(d, b), mul_(a, a));
		lemma_mul_comm(b, d);
		lemma_eq_ref(mul_(a, a));
	}
	let temp_78_0 = (mul_((mul_((mod_(c, m)), c)), (mul_(c, b))));
	let temp_78_1 = (mul_((mul_((mod_(c, m)), c)), (mul_(b, c))));
	assert(eq_(temp_78_0, temp_78_1)) by {
		cong_mul_(mul_(mod_(c, m), c), mul_(c, b), mul_(mod_(c, m), c), mul_(b, c));
		lemma_mul_comm(c, b);
		lemma_eq_ref(mul_(mod_(c, m), c));
	}
	let temp_79_0 = (mul_((add_(a, a)), (mul_(a, b))));
	let temp_79_1 = (mul_((add_(a, a)), (mul_(a, b))));
	assert(eq_(temp_79_0, temp_79_1)) by {
		lemma_eq_ref(temp_79_0);
	}
	let temp_80_0 = (mul_((mul_(a, c)), (mul_(b, d))));
	let temp_80_1 = (mul_((mul_(c, a)), (mul_(b, d))));
	assert(eq_(temp_80_0, temp_80_1)) by {
		cong_mul_(mul_(a, c), mul_(b, d), mul_(c, a), mul_(b, d));
		lemma_mul_comm(a, c);
		lemma_eq_ref(mul_(b, d));
	}
	let temp_81_0 = (sub_((mul_((mod_(d, m)), d)), (add_(c, b))));
	let temp_81_1 = (sub_((mul_((mod_(d, m)), d)), (add_(b, c))));
	assert(eq_(temp_81_0, temp_81_1)) by {
		lemma_add_comm(c, b);
		cong_sub_(mul_(mod_(d, m), d), add_(c, b), mul_(mod_(d, m), d), add_(b, c));
		lemma_eq_ref(mul_(mod_(d, m), d));
	}
	let temp_82_0 = (mul_((sub_(c, c)), (mul_(b, a))));
	let temp_82_1 = (mul_((mul_(b, a)), (sub_(c, c))));
	assert(eq_(temp_82_0, temp_82_1)) by {
		lemma_mul_comm(sub_(c, c), mul_(b, a));
	}
	let temp_83_0 = (mul_((mul_(d, a)), (add_(b, a))));
	let temp_83_1 = (add_((mul_((mul_(d, a)), b)), (mul_((mul_(d, a)), a))));
	assert(eq_(temp_83_0, temp_83_1)) by {
		lemma_mul_dist(mul_(d, a), b, a);
	}
	let temp_84_0 = (mul_((mul_(c, b)), (sub_(c, b))));
	let temp_84_1 = (mul_(c, (mul_(b, (sub_(c, b))))));
	assert(eq_(temp_84_0, temp_84_1)) by {
		lemma_eq_sym(temp_84_1, temp_84_0);
		lemma_mul_assoc(c, b, sub_(c, b));
	}
	let temp_85_0 = (sub_((mul_(c, b)), (mod_((add_(a, as_elem(23))), m))));
	let temp_85_1 = (sub_((mul_(b, c)), (mod_((add_(a, as_elem(23))), m))));
	assert(eq_(temp_85_0, temp_85_1)) by {
		lemma_mul_comm(c, b);
		cong_sub_(mul_(c, b), mod_(add_(a, as_elem(23)), m), mul_(b, c), mod_(add_(a, as_elem(23)), m));
		lemma_eq_ref(mod_(add_(a, as_elem(23)), m));
	}
	let temp_86_0 = (mod_((mul_((mul_(a, c)), (mul_(d, d)))), m));
	let temp_86_1 = (mod_((sub_((mul_((mul_(a, c)), (mul_(d, d)))), (mul_((mul_((mul_(d, d)), (mul_(c, d)))), m)))), m));
	assert(eq_(temp_86_0, temp_86_1)) by {
		lemma_mod_mul_vanish(mul_(mul_(a, c), mul_(d, d)), mul_(mul_(d, d), mul_(c, d)), m);
	}
	let temp_87_0 = (mul_((mul_(c, d)), (sub_(a, b))));
	let temp_87_1 = (mul_((sub_(a, b)), (mul_(c, d))));
	assert(eq_(temp_87_0, temp_87_1)) by {
		lemma_mul_comm(mul_(c, d), sub_(a, b));
	}
	let temp_88_0 = (mul_((mul_(b, a)), (mul_(d, d))));
	let temp_88_1 = (mul_(b, (mul_(a, (mul_(d, d))))));
	assert(eq_(temp_88_0, temp_88_1)) by {
		lemma_eq_sym(temp_88_1, temp_88_0);
		lemma_mul_assoc(b, a, mul_(d, d));
	}
	let temp_89_0 = (mod_((add_((mul_(b, d)), (mul_(c, a)))), m));
	let temp_89_1 = (mod_((add_((mod_((mul_(b, d)), m)), (mod_((mul_(c, a)), m)))), m));
	assert(eq_(temp_89_0, temp_89_1)) by {
		lemma_mod_add_noop(mul_(b, d), mul_(c, a), m);
	}
	let temp_90_0 = (mul_((mul_(a, b)), (mul_(c, b))));
	let temp_90_1 = (mul_((mul_(a, b)), (mul_(b, c))));
	assert(eq_(temp_90_0, temp_90_1)) by {
		cong_mul_(mul_(a, b), mul_(c, b), mul_(a, b), mul_(b, c));
		lemma_mul_comm(c, b);
		lemma_eq_ref(mul_(a, b));
	}
	let temp_91_0 = (mul_((mul_(b, d)), (mul_(b, b))));
	let temp_91_1 = (mul_((mul_(b, b)), (mul_(b, d))));
	assert(eq_(temp_91_0, temp_91_1)) by {
		lemma_mul_comm(mul_(b, d), mul_(b, b));
	}
	let temp_92_0 = (mul_((sub_(d, d)), (mod_((mul_(c, d)), m))));
	let temp_92_1 = (mul_((sub_(d, d)), (mod_((add_((mul_(c, d)), (mul_((mod_((add_((add_(b, a)), (mul_(d, c)))), m)), m)))), m))));
	assert(eq_(temp_92_0, temp_92_1)) by {
		lemma_mod_mul_vanish(mul_(c, d), mod_(add_(add_(b, a), mul_(d, c)), m), m);
		cong_mul_(sub_(d, d), mod_(mul_(c, d), m), sub_(d, d), mod_(add_(mul_(c, d), mul_(mod_(add_(add_(b, a), mul_(d, c)), m), m)), m));
		lemma_eq_ref(sub_(d, d));
	}
	let temp_93_0 = (mul_((mul_(d, d)), (mod_((mul_(d, d)), m))));
	let temp_93_1 = (mul_(d, (mul_(d, (mod_((mul_(d, d)), m))))));
	assert(eq_(temp_93_0, temp_93_1)) by {
		lemma_eq_sym(temp_93_1, temp_93_0);
		lemma_mul_assoc(d, d, mod_(mul_(d, d), m));
	}
	let temp_94_0 = (mul_((mul_(d, (mod_(as_elem(66), m)))), (mul_(a, a))));
	let temp_94_1 = (mul_((mul_((mul_(d, (mod_(as_elem(66), m)))), a)), a));
	assert(eq_(temp_94_0, temp_94_1)) by {
		lemma_mul_assoc(mul_(d, mod_(as_elem(66), m)), a, a);
	}
	let temp_95_0 = (add_((mul_(c, d)), (mul_(a, d))));
	let temp_95_1 = (add_((mul_(c, d)), (mul_(d, a))));
	assert(eq_(temp_95_0, temp_95_1)) by {
		cong_add_(mul_(c, d), mul_(a, d), mul_(c, d), mul_(d, a));
		lemma_mul_comm(a, d);
		lemma_eq_ref(mul_(c, d));
	}
	let temp_96_0 = (mul_((mul_(d, c)), (mul_(a, c))));
	let temp_96_1 = (mul_((mul_((mul_(d, c)), a)), c));
	assert(eq_(temp_96_0, temp_96_1)) by {
		lemma_mul_assoc(mul_(d, c), a, c);
	}
	let temp_97_0 = (sub_((mul_(d, c)), (mul_(a, c))));
	let temp_97_1 = (sub_((mul_(c, d)), (mul_(a, c))));
	assert(eq_(temp_97_0, temp_97_1)) by {
		cong_sub_(mul_(d, c), mul_(a, c), mul_(c, d), mul_(a, c));
		lemma_mul_comm(d, c);
		lemma_eq_ref(mul_(a, c));
	}
	let temp_98_0 = (mod_((mul_((mul_(d, c)), (mul_(c, b)))), m));
	let temp_98_1 = (mod_((add_((mul_((mul_(d, c)), (mul_(c, b)))), (mul_((add_((mul_(c, c)), (mul_(c, c)))), m)))), m));
	assert(eq_(temp_98_0, temp_98_1)) by {
		lemma_mod_mul_vanish(mul_(mul_(d, c), mul_(c, b)), add_(mul_(c, c), mul_(c, c)), m);
	}
	let temp_99_0 = (add_((mul_(b, b)), (mul_(d, b))));
	let temp_99_1 = (add_((mul_(d, b)), (mul_(b, b))));
	assert(eq_(temp_99_0, temp_99_1)) by {
		lemma_add_comm(mul_(b, b), mul_(d, b));
	}
	let temp_100_0 = (mul_((mul_(b, a)), (mod_((sub_(c, a)), m))));
	let temp_100_1 = (mul_((mod_((sub_(c, a)), m)), (mul_(b, a))));
	assert(eq_(temp_100_0, temp_100_1)) by {
		lemma_mul_comm(mul_(b, a), mod_(sub_(c, a), m));
	}
	let temp_101_0 = (mul_((mul_(a, d)), (sub_(c, d))));
	let temp_101_1 = (mul_(a, (mul_(d, (sub_(c, d))))));
	assert(eq_(temp_101_0, temp_101_1)) by {
		lemma_eq_sym(temp_101_1, temp_101_0);
		lemma_mul_assoc(a, d, sub_(c, d));
	}
	let temp_102_0 = (mul_((mul_((mod_(b, m)), b)), (mul_(c, b))));
	let temp_102_1 = (mul_((mul_((mod_((sub_(b, (mul_((mul_((mul_(d, d)), (mul_((mod_(c, m)), d)))), m)))), m)), b)), (mul_(c, b))));
	assert(eq_(temp_102_0, temp_102_1)) by {
		cong_mul_(mod_(b, m), b, mod_(sub_(b, mul_(mul_(mul_(d, d), mul_(mod_(c, m), d)), m)), m), b);
		lemma_eq_ref(mul_(c, b));
		lemma_eq_ref(b);
		lemma_mod_mul_vanish(b, mul_(mul_(d, d), mul_(mod_(c, m), d)), m);
		cong_mul_(mul_(mod_(b, m), b), mul_(c, b), mul_(mod_(sub_(b, mul_(mul_(mul_(d, d), mul_(mod_(c, m), d)), m)), m), b), mul_(c, b));
	}
	let temp_103_0 = (mul_((mul_(b, d)), (mod_((mul_(d, c)), m))));
	let temp_103_1 = (mul_((mod_((mul_(d, c)), m)), (mul_(b, d))));
	assert(eq_(temp_103_0, temp_103_1)) by {
		lemma_mul_comm(mul_(b, d), mod_(mul_(d, c), m));
	}
	let temp_104_0 = (mul_((mod_((mul_(b, (mod_(b, m)))), m)), (mul_(b, b))));
	let temp_104_1 = (mul_((mul_((mod_((mul_(b, (mod_(b, m)))), m)), b)), b));
	assert(eq_(temp_104_0, temp_104_1)) by {
		lemma_mul_assoc(mod_(mul_(b, mod_(b, m)), m), b, b);
	}
	let temp_105_0 = (mul_((mul_(b, a)), (mul_(as_elem(5), b))));
	let temp_105_1 = (mul_((mul_(a, b)), (mul_(as_elem(5), b))));
	assert(eq_(temp_105_0, temp_105_1)) by {
		cong_mul_(mul_(b, a), mul_(as_elem(5), b), mul_(a, b), mul_(as_elem(5), b));
		lemma_mul_comm(b, a);
		lemma_eq_ref(mul_(as_elem(5), b));
	}
	let temp_106_0 = (mul_((mul_(d, (mod_(a, m)))), (mul_(b, (mod_(a, m))))));
	let temp_106_1 = (mul_((mul_((mod_(a, m)), d)), (mul_(b, (mod_(a, m))))));
	assert(eq_(temp_106_0, temp_106_1)) by {
		lemma_mul_comm(d, mod_(a, m));
		cong_mul_(mul_(d, mod_(a, m)), mul_(b, mod_(a, m)), mul_(mod_(a, m), d), mul_(b, mod_(a, m)));
		lemma_eq_ref(mul_(b, mod_(a, m)));
	}
	let temp_107_0 = (mul_((mul_(a, c)), (mul_(c, c))));
	let temp_107_1 = (mul_((mul_((mul_(a, c)), c)), c));
	assert(eq_(temp_107_0, temp_107_1)) by {
		lemma_mul_assoc(mul_(a, c), c, c);
	}
	let temp_108_0 = (mul_((mul_(d, d)), (mul_(d, d))));
	let temp_108_1 = (mul_(d, (mul_(d, (mul_(d, d))))));
	assert(eq_(temp_108_0, temp_108_1)) by {
		lemma_eq_sym(temp_108_1, temp_108_0);
		lemma_mul_assoc(d, d, mul_(d, d));
	}
	let temp_109_0 = (mul_((mul_(d, a)), (mul_(b, b))));
	let temp_109_1 = (mul_((mul_(a, d)), (mul_(b, b))));
	assert(eq_(temp_109_0, temp_109_1)) by {
		cong_mul_(mul_(d, a), mul_(b, b), mul_(a, d), mul_(b, b));
		lemma_mul_comm(d, a);
		lemma_mul_comm(b, b);
	}

}

} // verus!