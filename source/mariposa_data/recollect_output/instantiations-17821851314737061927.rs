use builtin_macros::*;
// use builtin::*;
mod nl_basics;
use crate::nl_basics::*;
verus! {

pub proof fn free_0(a: Elem, b: Elem, c: Elem, d: Elem, m: Elem)
{
	let temp_0_0 = (mod_((add_((mod_((mul_(b, c)), m)), (mul_(d, b)))), m));
	let temp_0_1 = (mod_((add_((mod_((mul_(b, c)), m)), (mod_((mul_(d, b)), m)))), m));
	assert(eq_(temp_0_0, temp_0_1)) by {
		lemma_mod_add_noop(mod_(mul_(b, c), m), mul_(d, b), m);
	}
	let temp_1_0 = (mul_((sub_(d, c)), (mul_(d, d))));
	let temp_1_1 = (sub_((mul_(d, (mul_(d, d)))), (mul_(c, (mul_(d, d))))));
	assert(eq_(temp_1_0, temp_1_1)) by {
		lemma_mul_dist(mul_(d, d), d, c);
	}
	let temp_2_0 = (mul_((mul_(a, a)), (mul_(a, a))));
	let temp_2_1 = (mul_((mul_(a, a)), (mul_(a, a))));
	assert(eq_(temp_2_0, temp_2_1)) by {
		lemma_eq_ref(temp_2_0);
	}
	let temp_3_0 = (mul_(a, (mul_((mod_(a, m)), (mod_(d, m))))));
	let temp_3_1 = (mul_((mul_(a, (mod_(a, m)))), (mod_(d, m))));
	assert(eq_(temp_3_0, temp_3_1)) by {
		lemma_mul_assoc(a, mod_(a, m), mod_(d, m));
	}
	let temp_4_0 = (mul_((mul_(d, a)), (mul_(d, d))));
	let temp_4_1 = (mul_((mul_((mul_(d, a)), d)), d));
	assert(eq_(temp_4_0, temp_4_1)) by {
		lemma_mul_assoc(mul_(d, a), d, d);
	}
	let temp_5_0 = (mul_((mul_(c, d)), (mul_(b, a))));
	let temp_5_1 = (mul_((mul_(d, c)), (mul_(b, a))));
	assert(eq_(temp_5_0, temp_5_1)) by {
		cong_mul_(mul_(c, d), mul_(b, a), mul_(d, c), mul_(b, a));
		lemma_mul_comm(c, d);
		lemma_eq_ref(mul_(b, a));
	}
	let temp_6_0 = (mul_((sub_(c, d)), (mul_(d, d))));
	let temp_6_1 = (mul_((sub_(c, d)), (mul_(d, d))));
	assert(eq_(temp_6_0, temp_6_1)) by {
		lemma_eq_ref(temp_6_0);
	}
	let temp_7_0 = (mul_((mul_(c, d)), (mul_(c, c))));
	let temp_7_1 = (mul_(c, (mul_(d, (mul_(c, c))))));
	assert(eq_(temp_7_0, temp_7_1)) by {
		lemma_eq_sym(temp_7_1, temp_7_0);
		lemma_mul_assoc(c, d, mul_(c, c));
	}
	let temp_8_0 = (mul_((mul_(d, b)), (mul_(d, b))));
	let temp_8_1 = (mul_((mul_(d, b)), (mul_(b, d))));
	assert(eq_(temp_8_0, temp_8_1)) by {
		cong_mul_(mul_(d, b), mul_(d, b), mul_(d, b), mul_(b, d));
		lemma_mul_comm(d, b);
		lemma_eq_ref(mul_(d, b));
	}
	let temp_9_0 = (mod_((mul_((sub_(b, a)), (mul_(d, d)))), m));
	let temp_9_1 = (mod_((add_((mul_((sub_(b, a)), (mul_(d, d)))), (mul_((add_((mul_(d, d)), (mul_(b, c)))), m)))), m));
	assert(eq_(temp_9_0, temp_9_1)) by {
		lemma_mod_mul_vanish(mul_(sub_(b, a), mul_(d, d)), add_(mul_(d, d), mul_(b, c)), m);
	}
	let temp_10_0 = (mul_((mul_(a, b)), (mod_((mul_(b, b)), m))));
	let temp_10_1 = (mul_((mul_(a, b)), (mod_((add_((mul_((mul_((sub_(b, b)), (mod_((add_(c, a)), m)))), m)), (mul_(b, b)))), m))));
	assert(eq_(temp_10_0, temp_10_1)) by {
		lemma_mod_mul_vanish(mul_(b, b), mul_(sub_(b, b), mod_(add_(c, a), m)), m);
		cong_mul_(mul_(a, b), mod_(mul_(b, b), m), mul_(a, b), mod_(add_(mul_(mul_(sub_(b, b), mod_(add_(c, a), m)), m), mul_(b, b)), m));
		lemma_eq_ref(mul_(a, b));
	}
	let temp_11_0 = (mul_((mul_(b, (mod_(b, m)))), (mul_((mod_(d, m)), b))));
	let temp_11_1 = (mul_((mul_(b, (mod_((add_(b, (mul_((mul_((mul_(c, (mod_(d, m)))), (mul_(c, d)))), m)))), m)))), (mul_((mod_(d, m)), b))));
	assert(eq_(temp_11_0, temp_11_1)) by {
		lemma_mod_mul_vanish(b, mul_(mul_(c, mod_(d, m)), mul_(c, d)), m);
		cong_mul_(mul_(b, mod_(b, m)), mul_(mod_(d, m), b), mul_(b, mod_(add_(b, mul_(mul_(mul_(c, mod_(d, m)), mul_(c, d)), m)), m)), mul_(mod_(d, m), b));
		lemma_eq_ref(b);
		cong_mul_(b, mod_(b, m), b, mod_(add_(b, mul_(mul_(mul_(c, mod_(d, m)), mul_(c, d)), m)), m));
		lemma_eq_ref(mul_(mod_(d, m), b));
	}
	let temp_12_0 = (mod_((mul_((sub_((mod_(d, m)), b)), (add_(c, c)))), m));
	let temp_12_1 = (mod_((mul_((sub_((mod_((sub_(d, (mul_((mul_((mul_(c, b)), (mul_(a, b)))), m)))), m)), b)), (add_(c, c)))), m));
	assert(eq_(temp_12_0, temp_12_1)) by {
		lemma_add_comm(c, c);
		cong_mod_(mul_(sub_(mod_(d, m), b), add_(c, c)), m, mul_(sub_(mod_(sub_(d, mul_(mul_(mul_(c, b), mul_(a, b)), m)), m), b), add_(c, c)), m);
		lemma_mod_mul_vanish(d, mul_(mul_(c, b), mul_(a, b)), m);
		cong_mul_(sub_(mod_(d, m), b), add_(c, c), sub_(mod_(sub_(d, mul_(mul_(mul_(c, b), mul_(a, b)), m)), m), b), add_(c, c));
		cong_sub_(mod_(d, m), b, mod_(sub_(d, mul_(mul_(mul_(c, b), mul_(a, b)), m)), m), b);
		lemma_eq_ref(b);
		lemma_eq_ref(m);
	}
	let temp_13_0 = (mul_((mul_(a, b)), (mul_(d, as_elem(97)))));
	let temp_13_1 = (mul_((mul_(b, a)), (mul_(d, as_elem(97)))));
	assert(eq_(temp_13_0, temp_13_1)) by {
		lemma_mul_comm(a, b);
		cong_mul_(mul_(a, b), mul_(d, as_elem(97)), mul_(b, a), mul_(d, as_elem(97)));
		lemma_eq_ref(mul_(d, as_elem(97)));
	}
	let temp_14_0 = (mul_((mul_(d, c)), (mul_(a, c))));
	let temp_14_1 = (mul_(d, (mul_(c, (mul_(a, c))))));
	assert(eq_(temp_14_0, temp_14_1)) by {
		lemma_eq_sym(temp_14_1, temp_14_0);
		lemma_mul_assoc(d, c, mul_(a, c));
	}
	let temp_15_0 = (mul_((mul_(a, (mod_(c, m)))), (mul_(b, a))));
	let temp_15_1 = (mul_((mul_((mul_(a, (mod_(c, m)))), b)), a));
	assert(eq_(temp_15_0, temp_15_1)) by {
		lemma_mul_assoc(mul_(a, mod_(c, m)), b, a);
	}
	let temp_16_0 = (mul_((mul_(d, a)), (sub_(d, d))));
	let temp_16_1 = (mul_(d, (mul_(a, (sub_(d, d))))));
	assert(eq_(temp_16_0, temp_16_1)) by {
		lemma_eq_sym(temp_16_1, temp_16_0);
		lemma_mul_assoc(d, a, sub_(d, d));
	}
	let temp_17_0 = (mod_((mul_((mul_(b, c)), (mul_(c, d)))), m));
	let temp_17_1 = (mod_((add_((mul_((mul_((add_(a, (mod_(c, m)))), (mul_(a, a)))), m)), (mul_((mul_(b, c)), (mul_(c, d)))))), m));
	assert(eq_(temp_17_0, temp_17_1)) by {
		lemma_mod_mul_vanish(mul_(mul_(b, c), mul_(c, d)), mul_(add_(a, mod_(c, m)), mul_(a, a)), m);
	}
	let temp_18_0 = (mul_((mul_(as_elem(43), c)), (add_(d, b))));
	let temp_18_1 = (mul_((mul_(as_elem(43), c)), (add_(b, d))));
	assert(eq_(temp_18_0, temp_18_1)) by {
		lemma_add_comm(d, b);
		cong_mul_(mul_(as_elem(43), c), add_(d, b), mul_(as_elem(43), c), add_(b, d));
		lemma_eq_ref(mul_(as_elem(43), c));
	}
	let temp_19_0 = (mul_((mul_(c, c)), (add_(b, c))));
	let temp_19_1 = (mul_((add_(b, c)), (mul_(c, c))));
	assert(eq_(temp_19_0, temp_19_1)) by {
		lemma_mul_comm(mul_(c, c), add_(b, c));
	}
	let temp_20_0 = (mul_((mod_((mul_(c, d)), m)), (add_(d, c))));
	let temp_20_1 = (mul_((add_(d, c)), (mod_((mul_(c, d)), m))));
	assert(eq_(temp_20_0, temp_20_1)) by {
		lemma_mul_comm(mod_(mul_(c, d), m), add_(d, c));
	}
	let temp_21_0 = (mul_((sub_(d, a)), (mul_(d, b))));
	let temp_21_1 = (mul_((mul_((sub_(d, a)), d)), b));
	assert(eq_(temp_21_0, temp_21_1)) by {
		lemma_mul_assoc(sub_(d, a), d, b);
	}
	let temp_22_0 = (mul_((mul_(d, c)), (mod_((mul_((mod_(a, m)), c)), m))));
	let temp_22_1 = (mul_((mul_(d, c)), (mod_((mul_((mod_((add_(a, (mul_((sub_((sub_(b, d)), (mul_(d, a)))), m)))), m)), c)), m))));
	assert(eq_(temp_22_0, temp_22_1)) by {
		lemma_mod_mul_vanish(a, sub_(sub_(b, d), mul_(d, a)), m);
		cong_mul_(mul_(d, c), mod_(mul_(mod_(a, m), c), m), mul_(d, c), mod_(mul_(mod_(add_(a, mul_(sub_(sub_(b, d), mul_(d, a)), m)), m), c), m));
		cong_mod_(mul_(mod_(a, m), c), m, mul_(mod_(add_(a, mul_(sub_(sub_(b, d), mul_(d, a)), m)), m), c), m);
		lemma_eq_ref(mul_(d, c));
		lemma_eq_ref(c);
		cong_mul_(mod_(a, m), c, mod_(add_(a, mul_(sub_(sub_(b, d), mul_(d, a)), m)), m), c);
		lemma_eq_ref(m);
	}
	let temp_23_0 = (mul_((mul_(c, c)), (mul_((mod_(a, m)), b))));
	let temp_23_1 = (mul_((mul_((mul_(c, c)), (mod_(a, m)))), b));
	assert(eq_(temp_23_0, temp_23_1)) by {
		lemma_mul_assoc(mul_(c, c), mod_(a, m), b);
	}
	let temp_24_0 = (mul_((mul_(d, b)), (mul_(c, a))));
	let temp_24_1 = (mul_(d, (mul_(b, (mul_(c, a))))));
	assert(eq_(temp_24_0, temp_24_1)) by {
		lemma_eq_sym(temp_24_1, temp_24_0);
		lemma_mul_assoc(d, b, mul_(c, a));
	}
	let temp_25_0 = (add_((mul_(d, a)), (mul_(b, c))));
	let temp_25_1 = (add_((mul_(d, a)), (mul_(c, b))));
	assert(eq_(temp_25_0, temp_25_1)) by {
		cong_add_(mul_(d, a), mul_(b, c), mul_(d, a), mul_(c, b));
		lemma_mul_comm(b, c);
		lemma_eq_ref(mul_(d, a));
	}
	let temp_26_0 = (mul_((mul_(a, c)), (mul_(a, d))));
	let temp_26_1 = (mul_((mul_(c, a)), (mul_(a, d))));
	assert(eq_(temp_26_0, temp_26_1)) by {
		cong_mul_(mul_(a, c), mul_(a, d), mul_(c, a), mul_(a, d));
		lemma_mul_comm(a, c);
		lemma_eq_ref(mul_(a, d));
	}
	let temp_27_0 = (mul_((mul_(d, b)), (add_(a, b))));
	let temp_27_1 = (mul_((mul_(d, b)), (add_(b, a))));
	assert(eq_(temp_27_0, temp_27_1)) by {
		cong_mul_(mul_(d, b), add_(a, b), mul_(d, b), add_(b, a));
		lemma_add_comm(a, b);
		lemma_eq_ref(mul_(d, b));
	}
	let temp_28_0 = (add_((mul_((mod_(b, m)), a)), (add_((mod_(d, m)), c))));
	let temp_28_1 = (add_((mul_((mod_((add_((mul_((mul_((sub_(d, d)), (sub_(b, d)))), m)), b)), m)), a)), (add_((mod_(d, m)), c))));
	assert(eq_(temp_28_0, temp_28_1)) by {
		lemma_mod_mul_vanish(b, mul_(sub_(d, d), sub_(b, d)), m);
		cong_add_(mul_(mod_(b, m), a), add_(mod_(d, m), c), mul_(mod_(add_(mul_(mul_(sub_(d, d), sub_(b, d)), m), b), m), a), add_(mod_(d, m), c));
		lemma_eq_ref(a);
		cong_mul_(mod_(b, m), a, mod_(add_(mul_(mul_(sub_(d, d), sub_(b, d)), m), b), m), a);
		lemma_eq_ref(add_(mod_(d, m), c));
	}
	let temp_29_0 = (mul_((mul_(c, a)), (mul_(a, (mod_(b, m))))));
	let temp_29_1 = (mul_((mul_(a, c)), (mul_(a, (mod_(b, m))))));
	assert(eq_(temp_29_0, temp_29_1)) by {
		lemma_mul_comm(c, a);
		cong_mul_(mul_(c, a), mul_(a, mod_(b, m)), mul_(a, c), mul_(a, mod_(b, m)));
		lemma_eq_ref(mul_(a, mod_(b, m)));
	}
	let temp_30_0 = (mul_((mul_(a, a)), (mul_(a, c))));
	let temp_30_1 = (mul_((mul_(a, c)), (mul_(a, a))));
	assert(eq_(temp_30_0, temp_30_1)) by {
		lemma_mul_comm(mul_(a, a), mul_(a, c));
	}
	let temp_31_0 = (mul_((mul_(b, a)), (mul_((mod_(d, m)), d))));
	let temp_31_1 = (mul_((mul_(b, a)), (mul_((mod_((add_(d, (mul_((mul_((mul_(c, as_elem(73))), (mul_(a, d)))), m)))), m)), d))));
	assert(eq_(temp_31_0, temp_31_1)) by {
		lemma_mod_mul_vanish(d, mul_(mul_(c, as_elem(73)), mul_(a, d)), m);
		cong_mul_(mul_(b, a), mul_(mod_(d, m), d), mul_(b, a), mul_(mod_(add_(d, mul_(mul_(mul_(c, as_elem(73)), mul_(a, d)), m)), m), d));
		cong_mul_(mod_(d, m), d, mod_(add_(d, mul_(mul_(mul_(c, as_elem(73)), mul_(a, d)), m)), m), d);
		lemma_eq_ref(d);
		lemma_eq_ref(mul_(b, a));
	}
	let temp_32_0 = (mul_((mod_((mul_(b, d)), m)), (mul_((mod_(a, m)), d))));
	let temp_32_1 = (mul_((mul_((mod_((mul_(b, d)), m)), (mod_(a, m)))), d));
	assert(eq_(temp_32_0, temp_32_1)) by {
		lemma_mul_assoc(mod_(mul_(b, d), m), mod_(a, m), d);
	}
	let temp_33_0 = (mul_((mod_((add_(b, b)), m)), (mul_(b, a))));
	let temp_33_1 = (mul_((mul_((mod_((add_(b, b)), m)), b)), a));
	assert(eq_(temp_33_0, temp_33_1)) by {
		lemma_mul_assoc(mod_(add_(b, b), m), b, a);
	}
	let temp_34_0 = (mul_((mul_((mod_(a, m)), d)), (mul_((mod_(c, m)), a))));
	let temp_34_1 = (mul_((mul_((mod_(a, m)), d)), (mul_((mod_((sub_(c, (mul_((mul_((mul_(b, c)), (mul_(c, c)))), m)))), m)), a))));
	assert(eq_(temp_34_0, temp_34_1)) by {
		lemma_mod_mul_vanish(c, mul_(mul_(b, c), mul_(c, c)), m);
		cong_mul_(mul_(mod_(a, m), d), mul_(mod_(c, m), a), mul_(mod_(a, m), d), mul_(mod_(sub_(c, mul_(mul_(mul_(b, c), mul_(c, c)), m)), m), a));
		lemma_eq_ref(a);
		lemma_eq_ref(mul_(mod_(a, m), d));
		cong_mul_(mod_(c, m), a, mod_(sub_(c, mul_(mul_(mul_(b, c), mul_(c, c)), m)), m), a);
	}
	let temp_35_0 = (mod_((mul_((mul_((mod_(d, m)), b)), (mul_((mod_(a, m)), d)))), m));
	let temp_35_1 = (mod_((mul_((mul_((mod_(d, m)), b)), (mul_((mod_((sub_(a, (mul_((mul_((mul_(b, b)), (mul_(c, b)))), m)))), m)), d)))), m));
	assert(eq_(temp_35_0, temp_35_1)) by {
		lemma_mod_mul_vanish(a, mul_(mul_(b, b), mul_(c, b)), m);
		cong_mod_(mul_(mul_(mod_(d, m), b), mul_(mod_(a, m), d)), m, mul_(mul_(mod_(d, m), b), mul_(mod_(sub_(a, mul_(mul_(mul_(b, b), mul_(c, b)), m)), m), d)), m);
		lemma_eq_ref(mul_(mod_(d, m), b));
		lemma_eq_ref(m);
		cong_mul_(mul_(mod_(d, m), b), mul_(mod_(a, m), d), mul_(mod_(d, m), b), mul_(mod_(sub_(a, mul_(mul_(mul_(b, b), mul_(c, b)), m)), m), d));
		cong_mul_(mod_(a, m), d, mod_(sub_(a, mul_(mul_(mul_(b, b), mul_(c, b)), m)), m), d);
		lemma_eq_ref(d);
	}
	let temp_36_0 = (mul_((mul_(c, a)), (sub_(a, b))));
	let temp_36_1 = (mul_((sub_(a, b)), (mul_(c, a))));
	assert(eq_(temp_36_0, temp_36_1)) by {
		lemma_mul_comm(mul_(c, a), sub_(a, b));
	}
	let temp_37_0 = (mul_((mul_(d, b)), (mul_(c, a))));
	let temp_37_1 = (mul_((mul_(c, a)), (mul_(d, b))));
	assert(eq_(temp_37_0, temp_37_1)) by {
		lemma_mul_comm(mul_(d, b), mul_(c, a));
	}
	let temp_38_0 = (mul_((mul_(b, a)), (mul_(as_elem(88), a))));
	let temp_38_1 = (mul_((mul_(as_elem(88), a)), (mul_(b, a))));
	assert(eq_(temp_38_0, temp_38_1)) by {
		lemma_mul_comm(mul_(b, a), mul_(as_elem(88), a));
	}
	let temp_39_0 = (mul_((mul_(b, c)), (mul_(b, d))));
	let temp_39_1 = (mul_(b, (mul_(c, (mul_(b, d))))));
	assert(eq_(temp_39_0, temp_39_1)) by {
		lemma_eq_sym(temp_39_1, temp_39_0);
		lemma_mul_assoc(b, c, mul_(b, d));
	}
	let temp_40_0 = (mul_((mul_(d, d)), d));
	let temp_40_1 = (mul_(d, (mul_(d, d))));
	assert(eq_(temp_40_0, temp_40_1)) by {
		lemma_mul_comm(mul_(d, d), d);
	}
	let temp_41_0 = (mul_((mul_(b, b)), (add_(d, a))));
	let temp_41_1 = (mul_((mul_(b, b)), (add_(a, d))));
	assert(eq_(temp_41_0, temp_41_1)) by {
		cong_mul_(mul_(b, b), add_(d, a), mul_(b, b), add_(a, d));
		lemma_add_comm(d, a);
		lemma_mul_comm(b, b);
	}
	let temp_42_0 = (sub_((mul_(c, d)), (mul_(c, (mod_(c, m))))));
	let temp_42_1 = (sub_((mul_(d, c)), (mul_(c, (mod_(c, m))))));
	assert(eq_(temp_42_0, temp_42_1)) by {
		cong_sub_(mul_(c, d), mul_(c, mod_(c, m)), mul_(d, c), mul_(c, mod_(c, m)));
		lemma_mul_comm(c, d);
		lemma_eq_ref(mul_(c, mod_(c, m)));
	}
	let temp_43_0 = (mul_((mul_(a, c)), (mul_(b, d))));
	let temp_43_1 = (mul_((mul_(b, d)), (mul_(a, c))));
	assert(eq_(temp_43_0, temp_43_1)) by {
		lemma_mul_comm(mul_(a, c), mul_(b, d));
	}
	let temp_44_0 = (mul_((add_(c, a)), (add_(d, c))));
	let temp_44_1 = (add_((mul_(c, (add_(d, c)))), (mul_(a, (add_(d, c))))));
	assert(eq_(temp_44_0, temp_44_1)) by {
		lemma_mul_dist(c, a, add_(d, c));
	}
	let temp_45_0 = (mod_((mul_((mul_(a, d)), (mul_(a, c)))), m));
	let temp_45_1 = (mod_((add_((mul_((mul_((mul_(d, d)), (mul_(c, b)))), m)), (mul_((mul_(a, d)), (mul_(a, c)))))), m));
	assert(eq_(temp_45_0, temp_45_1)) by {
		lemma_mod_mul_vanish(mul_(mul_(a, d), mul_(a, c)), mul_(mul_(d, d), mul_(c, b)), m);
	}
	let temp_46_0 = (mul_((mul_(d, d)), (sub_(c, c))));
	let temp_46_1 = (mul_((sub_(c, c)), (mul_(d, d))));
	assert(eq_(temp_46_0, temp_46_1)) by {
		lemma_mul_comm(mul_(d, d), sub_(c, c));
	}
	let temp_47_0 = (add_((sub_(d, a)), (mod_((add_(c, c)), m))));
	let temp_47_1 = (add_((sub_(d, a)), (mod_((add_((mul_((mul_((mul_(b, d)), (mul_(c, d)))), m)), (add_(c, c)))), m))));
	assert(eq_(temp_47_0, temp_47_1)) by {
		lemma_mod_mul_vanish(add_(c, c), mul_(mul_(b, d), mul_(c, d)), m);
		cong_add_(sub_(d, a), mod_(add_(c, c), m), sub_(d, a), mod_(add_(mul_(mul_(mul_(b, d), mul_(c, d)), m), add_(c, c)), m));
		lemma_eq_ref(sub_(d, a));
	}
	let temp_48_0 = (mul_((mul_(b, b)), (mul_(d, b))));
	let temp_48_1 = (mul_(b, (mul_(b, (mul_(d, b))))));
	assert(eq_(temp_48_0, temp_48_1)) by {
		lemma_eq_sym(temp_48_1, temp_48_0);
		lemma_mul_assoc(b, b, mul_(d, b));
	}
	let temp_49_0 = (mul_((sub_(a, a)), (mul_(d, b))));
	let temp_49_1 = (mul_((mul_((sub_(a, a)), d)), b));
	assert(eq_(temp_49_0, temp_49_1)) by {
		lemma_mul_assoc(sub_(a, a), d, b);
	}
	let temp_50_0 = (mul_((mul_(d, c)), (mul_(a, b))));
	let temp_50_1 = (mul_((mul_(a, b)), (mul_(d, c))));
	assert(eq_(temp_50_0, temp_50_1)) by {
		lemma_mul_comm(mul_(d, c), mul_(a, b));
	}
	let temp_51_0 = (mul_((sub_(d, c)), (mul_(a, a))));
	let temp_51_1 = (sub_((mul_(d, (mul_(a, a)))), (mul_(c, (mul_(a, a))))));
	assert(eq_(temp_51_0, temp_51_1)) by {
		lemma_mul_dist(mul_(a, a), d, c);
	}
	let temp_52_0 = (mul_((sub_((mod_(b, m)), d)), (add_(b, a))));
	let temp_52_1 = (mul_((sub_((mod_(b, m)), d)), (add_(a, b))));
	assert(eq_(temp_52_0, temp_52_1)) by {
		lemma_add_comm(b, a);
		cong_mul_(sub_(mod_(b, m), d), add_(b, a), sub_(mod_(b, m), d), add_(a, b));
		lemma_eq_ref(sub_(mod_(b, m), d));
	}
	let temp_53_0 = (mul_((mul_((mod_(as_elem(70), m)), d)), (mul_(d, a))));
	let temp_53_1 = (mul_((mul_((mod_((sub_(as_elem(70), (mul_((mul_((mul_(c, b)), (mul_((mod_(c, m)), a)))), m)))), m)), d)), (mul_(d, a))));
	assert(eq_(temp_53_0, temp_53_1)) by {
		lemma_mod_mul_vanish(as_elem(70), mul_(mul_(c, b), mul_(mod_(c, m), a)), m);
		cong_mul_(mul_(mod_(as_elem(70), m), d), mul_(d, a), mul_(mod_(sub_(as_elem(70), mul_(mul_(mul_(c, b), mul_(mod_(c, m), a)), m)), m), d), mul_(d, a));
		lemma_eq_ref(d);
		lemma_eq_ref(mul_(d, a));
		cong_mul_(mod_(as_elem(70), m), d, mod_(sub_(as_elem(70), mul_(mul_(mul_(c, b), mul_(mod_(c, m), a)), m)), m), d);
	}
	let temp_54_0 = (mul_((mul_(a, b)), (mul_(a, c))));
	let temp_54_1 = (mul_((mul_((mul_(a, b)), a)), c));
	assert(eq_(temp_54_0, temp_54_1)) by {
		lemma_mul_assoc(mul_(a, b), a, c);
	}
	let temp_55_0 = (mul_((mul_(c, b)), (mul_(a, (mod_(c, m))))));
	let temp_55_1 = (mul_((mul_(b, c)), (mul_(a, (mod_(c, m))))));
	assert(eq_(temp_55_0, temp_55_1)) by {
		lemma_mul_comm(c, b);
		cong_mul_(mul_(c, b), mul_(a, mod_(c, m)), mul_(b, c), mul_(a, mod_(c, m)));
		lemma_eq_ref(mul_(a, mod_(c, m)));
	}
	let temp_56_0 = (sub_(b, (mul_(b, d))));
	let temp_56_1 = (sub_(b, (mul_(d, b))));
	assert(eq_(temp_56_0, temp_56_1)) by {
		cong_sub_(b, mul_(b, d), b, mul_(d, b));
		lemma_mul_comm(b, d);
		lemma_eq_ref(b);
	}
	let temp_57_0 = (mul_((mul_(d, (mod_(b, m)))), (sub_(a, d))));
	let temp_57_1 = (mul_((sub_(a, d)), (mul_(d, (mod_(b, m))))));
	assert(eq_(temp_57_0, temp_57_1)) by {
		lemma_mul_comm(mul_(d, mod_(b, m)), sub_(a, d));
	}
	let temp_58_0 = (mul_((mul_(c, d)), (mul_(c, b))));
	let temp_58_1 = (mul_((mul_(c, d)), (mul_(b, c))));
	assert(eq_(temp_58_0, temp_58_1)) by {
		cong_mul_(mul_(c, d), mul_(c, b), mul_(c, d), mul_(b, c));
		lemma_mul_comm(c, b);
		lemma_eq_ref(mul_(c, d));
	}
	let temp_59_0 = (mul_((add_(b, b)), (mul_(a, a))));
	let temp_59_1 = (add_((mul_(b, (mul_(a, a)))), (mul_(b, (mul_(a, a))))));
	assert(eq_(temp_59_0, temp_59_1)) by {
		lemma_mul_dist(b, b, mul_(a, a));
	}
	let temp_60_0 = (mul_((mod_((mul_(c, (mod_(d, m)))), m)), (sub_(b, (mod_(b, m))))));
	let temp_60_1 = (mul_((mod_((mul_((mod_(d, m)), c)), m)), (sub_(b, (mod_(b, m))))));
	assert(eq_(temp_60_0, temp_60_1)) by {
		lemma_mul_comm(c, mod_(d, m));
		cong_mul_(mod_(mul_(c, mod_(d, m)), m), sub_(b, mod_(b, m)), mod_(mul_(mod_(d, m), c), m), sub_(b, mod_(b, m)));
		lemma_eq_ref(m);
		cong_mod_(mul_(c, mod_(d, m)), m, mul_(mod_(d, m), c), m);
		lemma_eq_ref(sub_(b, mod_(b, m)));
	}
	let temp_61_0 = (add_((mul_(a, a)), (mul_(a, a))));
	let temp_61_1 = (add_((mul_(a, a)), (mul_(a, a))));
	assert(eq_(temp_61_0, temp_61_1)) by {
		lemma_eq_ref(temp_61_0);
	}
	let temp_62_0 = (mul_((add_(d, b)), (add_(b, d))));
	let temp_62_1 = (mul_((add_(d, b)), (add_(d, b))));
	assert(eq_(temp_62_0, temp_62_1)) by {
		cong_mul_(add_(d, b), add_(b, d), add_(d, b), add_(d, b));
		lemma_add_comm(b, d);
		lemma_eq_ref(add_(d, b));
	}
	let temp_63_0 = (add_((mul_(c, d)), (sub_(a, d))));
	let temp_63_1 = (add_((sub_(a, d)), (mul_(c, d))));
	assert(eq_(temp_63_0, temp_63_1)) by {
		lemma_add_comm(mul_(c, d), sub_(a, d));
	}
	let temp_64_0 = (mul_((mul_(b, b)), (mul_(c, d))));
	let temp_64_1 = (mul_((mul_(b, b)), (mul_(c, d))));
	assert(eq_(temp_64_0, temp_64_1)) by {
		lemma_eq_ref(temp_64_0);
	}
	let temp_65_0 = (mod_((mul_((mod_((mul_(a, d)), m)), (mul_(b, a)))), m));
	let temp_65_1 = (mod_((mul_((mod_((add_((mul_(a, d)), (mul_((mul_((mul_(b, c)), (mul_((mod_(d, m)), d)))), m)))), m)), (mul_(b, a)))), m));
	assert(eq_(temp_65_0, temp_65_1)) by {
		lemma_mod_mul_vanish(mul_(a, d), mul_(mul_(b, c), mul_(mod_(d, m), d)), m);
		cong_mod_(mul_(mod_(mul_(a, d), m), mul_(b, a)), m, mul_(mod_(add_(mul_(a, d), mul_(mul_(mul_(b, c), mul_(mod_(d, m), d)), m)), m), mul_(b, a)), m);
		lemma_eq_ref(mul_(b, a));
		lemma_eq_ref(m);
		cong_mul_(mod_(mul_(a, d), m), mul_(b, a), mod_(add_(mul_(a, d), mul_(mul_(mul_(b, c), mul_(mod_(d, m), d)), m)), m), mul_(b, a));
	}
	let temp_66_0 = (mul_((add_(c, (mod_(a, m)))), (mul_(c, as_elem(56)))));
	let temp_66_1 = (add_((mul_(c, (mul_(c, as_elem(56))))), (mul_((mod_(a, m)), (mul_(c, as_elem(56)))))));
	assert(eq_(temp_66_0, temp_66_1)) by {
		lemma_mul_dist(c, mod_(a, m), mul_(c, as_elem(56)));
	}
	let temp_67_0 = (mul_((mod_((mul_(a, d)), m)), (add_(b, b))));
	let temp_67_1 = (mul_((add_(b, b)), (mod_((mul_(a, d)), m))));
	assert(eq_(temp_67_0, temp_67_1)) by {
		lemma_mul_comm(mod_(mul_(a, d), m), add_(b, b));
	}
	let temp_68_0 = (mul_((mul_(c, c)), (mul_(a, a))));
	let temp_68_1 = (mul_((mul_(c, c)), (mul_(a, a))));
	assert(eq_(temp_68_0, temp_68_1)) by {
		lemma_eq_ref(temp_68_0);
	}
	let temp_69_0 = (add_((mul_(d, c)), (mul_(c, d))));
	let temp_69_1 = (add_((mul_(c, d)), (mul_(c, d))));
	assert(eq_(temp_69_0, temp_69_1)) by {
		cong_add_(mul_(d, c), mul_(c, d), mul_(c, d), mul_(c, d));
		lemma_mul_comm(d, c);
		lemma_eq_ref(mul_(c, d));
	}
	let temp_70_0 = (mul_((mul_(a, c)), (mod_((mul_(b, b)), m))));
	let temp_70_1 = (mul_((mul_(a, c)), (mod_((sub_((mul_(b, b)), (mul_((mul_((mod_((mul_(b, d)), m)), (mul_(a, (mod_(b, m)))))), m)))), m))));
	assert(eq_(temp_70_0, temp_70_1)) by {
		lemma_mod_mul_vanish(mul_(b, b), mul_(mod_(mul_(b, d), m), mul_(a, mod_(b, m))), m);
		cong_mul_(mul_(a, c), mod_(mul_(b, b), m), mul_(a, c), mod_(sub_(mul_(b, b), mul_(mul_(mod_(mul_(b, d), m), mul_(a, mod_(b, m))), m)), m));
		lemma_eq_ref(mul_(a, c));
	}
	let temp_71_0 = (mul_((mul_(d, d)), (mul_(c, b))));
	let temp_71_1 = (mul_((mul_(c, b)), (mul_(d, d))));
	assert(eq_(temp_71_0, temp_71_1)) by {
		lemma_mul_comm(mul_(d, d), mul_(c, b));
	}
	let temp_72_0 = (mod_((sub_((mul_(b, b)), (mul_(d, d)))), m));
	let temp_72_1 = (mod_((sub_((sub_((mul_(b, b)), (mul_(d, d)))), (mul_((mul_((mul_(a, d)), (mul_(b, b)))), m)))), m));
	assert(eq_(temp_72_0, temp_72_1)) by {
		lemma_mod_mul_vanish(sub_(mul_(b, b), mul_(d, d)), mul_(mul_(a, d), mul_(b, b)), m);
	}
	let temp_73_0 = (sub_((mul_(a, b)), (sub_(c, (mod_(c, m))))));
	let temp_73_1 = (sub_((mul_(a, b)), (sub_(c, (mod_((sub_(c, (mul_((mul_((mod_((mul_(c, a)), m)), (mul_(d, a)))), m)))), m))))));
	assert(eq_(temp_73_0, temp_73_1)) by {
		lemma_mod_mul_vanish(c, mul_(mod_(mul_(c, a), m), mul_(d, a)), m);
		cong_sub_(mul_(a, b), sub_(c, mod_(c, m)), mul_(a, b), sub_(c, mod_(sub_(c, mul_(mul_(mod_(mul_(c, a), m), mul_(d, a)), m)), m)));
		cong_sub_(c, mod_(c, m), c, mod_(sub_(c, mul_(mul_(mod_(mul_(c, a), m), mul_(d, a)), m)), m));
		lemma_eq_ref(mul_(a, b));
		lemma_eq_ref(c);
	}
	let temp_74_0 = (mul_((mul_(c, b)), (add_(b, a))));
	let temp_74_1 = (add_((mul_((mul_(c, b)), b)), (mul_((mul_(c, b)), a))));
	assert(eq_(temp_74_0, temp_74_1)) by {
		lemma_mul_dist(mul_(c, b), b, a);
	}
	let temp_75_0 = (mul_((mul_(a, c)), (sub_(b, d))));
	let temp_75_1 = (mul_((sub_(b, d)), (mul_(a, c))));
	assert(eq_(temp_75_0, temp_75_1)) by {
		lemma_mul_comm(mul_(a, c), sub_(b, d));
	}
	let temp_76_0 = (mul_((add_((mod_(a, m)), c)), (sub_((mod_(b, m)), d))));
	let temp_76_1 = (mul_((add_((mod_((add_(a, (mul_((mul_((mul_(a, b)), (sub_(a, (mod_(d, m)))))), m)))), m)), c)), (sub_((mod_(b, m)), d))));
	assert(eq_(temp_76_0, temp_76_1)) by {
		lemma_mod_mul_vanish(a, mul_(mul_(a, b), sub_(a, mod_(d, m))), m);
		cong_mul_(add_(mod_(a, m), c), sub_(mod_(b, m), d), add_(mod_(add_(a, mul_(mul_(mul_(a, b), sub_(a, mod_(d, m))), m)), m), c), sub_(mod_(b, m), d));
		lemma_eq_ref(c);
		cong_add_(mod_(a, m), c, mod_(add_(a, mul_(mul_(mul_(a, b), sub_(a, mod_(d, m))), m)), m), c);
		lemma_eq_ref(sub_(mod_(b, m), d));
	}
	let temp_77_0 = (mod_((mul_((mul_(c, c)), (mul_(b, d)))), m));
	let temp_77_1 = (mod_((sub_((mul_((mul_(c, c)), (mul_(b, d)))), (mul_((mul_((mul_(a, d)), (add_(c, (mod_(d, m)))))), m)))), m));
	assert(eq_(temp_77_0, temp_77_1)) by {
		lemma_mod_mul_vanish(mul_(mul_(c, c), mul_(b, d)), mul_(mul_(a, d), add_(c, mod_(d, m))), m);
	}
	let temp_78_0 = (mul_((mod_((mul_(c, d)), m)), (mul_(a, c))));
	let temp_78_1 = (mul_((mul_((mod_((mul_(c, d)), m)), a)), c));
	assert(eq_(temp_78_0, temp_78_1)) by {
		lemma_mul_assoc(mod_(mul_(c, d), m), a, c);
	}
	let temp_79_0 = (sub_((mul_(c, as_elem(16))), (mul_(d, a))));
	let temp_79_1 = (sub_((mul_(as_elem(16), c)), (mul_(d, a))));
	assert(eq_(temp_79_0, temp_79_1)) by {
		lemma_mul_comm(c, as_elem(16));
		cong_sub_(mul_(c, as_elem(16)), mul_(d, a), mul_(as_elem(16), c), mul_(d, a));
		lemma_eq_ref(mul_(d, a));
	}
	let temp_80_0 = (mod_((mul_((mod_((sub_(b, a)), m)), (mul_(as_elem(56), a)))), m));
	let temp_80_1 = (mod_((mul_((mod_((sub_((sub_(b, a)), (mul_((mul_((mul_(d, as_elem(81))), (mul_(b, a)))), m)))), m)), (mul_(as_elem(56), a)))), m));
	assert(eq_(temp_80_0, temp_80_1)) by {
		lemma_mod_mul_vanish(sub_(b, a), mul_(mul_(d, as_elem(81)), mul_(b, a)), m);
		cong_mod_(mul_(mod_(sub_(b, a), m), mul_(as_elem(56), a)), m, mul_(mod_(sub_(sub_(b, a), mul_(mul_(mul_(d, as_elem(81)), mul_(b, a)), m)), m), mul_(as_elem(56), a)), m);
		lemma_eq_ref(m);
		lemma_eq_ref(mul_(as_elem(56), a));
		cong_mul_(mod_(sub_(b, a), m), mul_(as_elem(56), a), mod_(sub_(sub_(b, a), mul_(mul_(mul_(d, as_elem(81)), mul_(b, a)), m)), m), mul_(as_elem(56), a));
	}
	let temp_81_0 = (mul_((mul_(c, c)), (mul_(b, d))));
	let temp_81_1 = (mul_(c, (mul_(c, (mul_(b, d))))));
	assert(eq_(temp_81_0, temp_81_1)) by {
		lemma_eq_sym(temp_81_1, temp_81_0);
		lemma_mul_assoc(c, c, mul_(b, d));
	}
	let temp_82_0 = (mul_((mul_(b, a)), (mul_(c, b))));
	let temp_82_1 = (mul_((mul_(c, b)), (mul_(b, a))));
	assert(eq_(temp_82_0, temp_82_1)) by {
		lemma_mul_comm(mul_(b, a), mul_(c, b));
	}
	let temp_83_0 = (mul_((mul_(c, b)), (mul_((mod_(d, m)), (mod_(c, m))))));
	let temp_83_1 = (mul_((mul_(c, b)), (mul_((mod_(d, m)), (mod_((add_(c, (mul_((mul_((mul_(d, b)), (mul_(b, b)))), m)))), m))))));
	assert(eq_(temp_83_0, temp_83_1)) by {
		lemma_mod_mul_vanish(c, mul_(mul_(d, b), mul_(b, b)), m);
		cong_mul_(mul_(c, b), mul_(mod_(d, m), mod_(c, m)), mul_(c, b), mul_(mod_(d, m), mod_(add_(c, mul_(mul_(mul_(d, b), mul_(b, b)), m)), m)));
		lemma_eq_ref(mul_(c, b));
		cong_mul_(mod_(d, m), mod_(c, m), mod_(d, m), mod_(add_(c, mul_(mul_(mul_(d, b), mul_(b, b)), m)), m));
		lemma_eq_ref(mod_(d, m));
	}
	let temp_84_0 = (mul_((mul_(b, d)), (mul_(d, b))));
	let temp_84_1 = (mul_((mul_(b, d)), (mul_(b, d))));
	assert(eq_(temp_84_0, temp_84_1)) by {
		cong_mul_(mul_(b, d), mul_(d, b), mul_(b, d), mul_(b, d));
		lemma_mul_comm(d, b);
		lemma_eq_ref(mul_(b, d));
	}
	let temp_85_0 = (mul_((sub_(c, a)), (mul_(c, a))));
	let temp_85_1 = (sub_((mul_(c, (mul_(c, a)))), (mul_(a, (mul_(c, a))))));
	assert(eq_(temp_85_0, temp_85_1)) by {
		lemma_mul_dist(mul_(c, a), c, a);
	}
	let temp_86_0 = (mul_((sub_(d, d)), (sub_((mod_(c, m)), a))));
	let temp_86_1 = (mul_((sub_((mod_(c, m)), a)), (sub_(d, d))));
	assert(eq_(temp_86_0, temp_86_1)) by {
		lemma_mul_comm(sub_(d, d), sub_(mod_(c, m), a));
	}
	let temp_87_0 = (mod_((mul_((mul_(as_elem(97), a)), (mul_(a, a)))), m));
	let temp_87_1 = (mod_((mul_((mul_(a, a)), (mul_(as_elem(97), a)))), m));
	assert(eq_(temp_87_0, temp_87_1)) by {
		lemma_mul_comm(mul_(as_elem(97), a), mul_(a, a));
		cong_mod_(mul_(mul_(as_elem(97), a), mul_(a, a)), m, mul_(mul_(a, a), mul_(as_elem(97), a)), m);
		lemma_eq_ref(m);
	}
	let temp_88_0 = (mul_((mul_(c, a)), (mul_(a, a))));
	let temp_88_1 = (mul_(c, (mul_(a, (mul_(a, a))))));
	assert(eq_(temp_88_0, temp_88_1)) by {
		lemma_eq_sym(temp_88_1, temp_88_0);
		lemma_mul_assoc(c, a, mul_(a, a));
	}
	let temp_89_0 = (mod_((mul_((mul_(c, a)), (mul_(b, (mod_(a, m)))))), m));
	let temp_89_1 = (mod_((mul_((mul_(c, a)), (mul_(b, (mod_((add_((mul_((mod_((sub_((mul_(b, d)), (mod_((mul_(d, b)), m)))), m)), m)), a)), m)))))), m));
	assert(eq_(temp_89_0, temp_89_1)) by {
		lemma_mod_mul_vanish(a, mod_(sub_(mul_(b, d), mod_(mul_(d, b), m)), m), m);
		cong_mod_(mul_(mul_(c, a), mul_(b, mod_(a, m))), m, mul_(mul_(c, a), mul_(b, mod_(add_(mul_(mod_(sub_(mul_(b, d), mod_(mul_(d, b), m)), m), m), a), m))), m);
		lemma_eq_ref(b);
		cong_mul_(mul_(c, a), mul_(b, mod_(a, m)), mul_(c, a), mul_(b, mod_(add_(mul_(mod_(sub_(mul_(b, d), mod_(mul_(d, b), m)), m), m), a), m)));
		lemma_eq_ref(mul_(c, a));
		lemma_eq_ref(m);
		cong_mul_(b, mod_(a, m), b, mod_(add_(mul_(mod_(sub_(mul_(b, d), mod_(mul_(d, b), m)), m), m), a), m));
	}
	let temp_90_0 = (mul_((mul_((mod_(as_elem(43), m)), d)), (mul_(d, c))));
	let temp_90_1 = (mul_((mul_(d, (mod_(as_elem(43), m)))), (mul_(d, c))));
	assert(eq_(temp_90_0, temp_90_1)) by {
		lemma_mul_comm(mod_(as_elem(43), m), d);
		cong_mul_(mul_(mod_(as_elem(43), m), d), mul_(d, c), mul_(d, mod_(as_elem(43), m)), mul_(d, c));
		lemma_eq_ref(mul_(d, c));
	}
	let temp_91_0 = (add_((mul_(a, b)), (mod_((mul_(a, d)), m))));
	let temp_91_1 = (add_((mul_(a, b)), (mod_((mul_(d, a)), m))));
	assert(eq_(temp_91_0, temp_91_1)) by {
		lemma_mul_comm(a, d);
		cong_add_(mul_(a, b), mod_(mul_(a, d), m), mul_(a, b), mod_(mul_(d, a), m));
		lemma_eq_ref(m);
		lemma_eq_ref(mul_(a, b));
		cong_mod_(mul_(a, d), m, mul_(d, a), m);
	}
	let temp_92_0 = (mul_((mul_(d, as_elem(35))), (mul_(c, a))));
	let temp_92_1 = (mul_((mul_(d, as_elem(35))), (mul_(a, c))));
	assert(eq_(temp_92_0, temp_92_1)) by {
		lemma_mul_comm(c, a);
		cong_mul_(mul_(d, as_elem(35)), mul_(c, a), mul_(d, as_elem(35)), mul_(a, c));
		lemma_eq_ref(mul_(d, as_elem(35)));
	}

}

} // verus!