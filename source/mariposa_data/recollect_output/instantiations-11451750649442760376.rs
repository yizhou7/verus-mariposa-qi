use builtin_macros::*;
// use builtin::*;
mod nl_basics;
use crate::nl_basics::*;
verus! {

pub proof fn free_0(a: Elem, b: Elem, c: Elem, d: Elem, m: Elem)
{
	let temp_0_0 = (sub_((mul_(a, (mod_(as_elem(34), m)))), (sub_(a, c))));
	let temp_0_1 = (sub_((mul_(a, (mod_((add_(as_elem(34), (mul_((sub_((mul_(c, d)), (mod_((mul_(a, a)), m)))), m)))), m)))), (sub_(a, c))));
	assert(eq_(temp_0_0, temp_0_1)) by {
		lemma_mod_mul_vanish(as_elem(34), sub_(mul_(c, d), mod_(mul_(a, a), m)), m);
		cong_sub_(mul_(a, mod_(as_elem(34), m)), sub_(a, c), mul_(a, mod_(add_(as_elem(34), mul_(sub_(mul_(c, d), mod_(mul_(a, a), m)), m)), m)), sub_(a, c));
		lemma_eq_ref(a);
		cong_mul_(a, mod_(as_elem(34), m), a, mod_(add_(as_elem(34), mul_(sub_(mul_(c, d), mod_(mul_(a, a), m)), m)), m));
		lemma_eq_ref(sub_(a, c));
	}
	let temp_1_0 = (mul_((mul_(as_elem(83), d)), (add_(c, a))));
	let temp_1_1 = (mul_(as_elem(83), (mul_(d, (add_(c, a))))));
	assert(eq_(temp_1_0, temp_1_1)) by {
		lemma_mul_assoc(as_elem(83), d, add_(c, a));
		lemma_eq_sym(temp_1_1, temp_1_0);
	}
	let temp_2_0 = (mul_((mod_((add_(b, b)), m)), (mul_(c, b))));
	let temp_2_1 = (mul_((mod_((sub_((add_(b, b)), (mul_((mul_((add_((mod_(c, m)), d)), (mul_((mod_(as_elem(38), m)), b)))), m)))), m)), (mul_(c, b))));
	assert(eq_(temp_2_0, temp_2_1)) by {
		cong_mul_(mod_(add_(b, b), m), mul_(c, b), mod_(sub_(add_(b, b), mul_(mul_(add_(mod_(c, m), d), mul_(mod_(as_elem(38), m), b)), m)), m), mul_(c, b));
		lemma_mod_mul_vanish(add_(b, b), mul_(add_(mod_(c, m), d), mul_(mod_(as_elem(38), m), b)), m);
		lemma_eq_ref(mul_(c, b));
	}
	let temp_3_0 = (mul_((mul_(b, a)), (mul_(d, a))));
	let temp_3_1 = (mul_((mul_((mul_(b, a)), d)), a));
	assert(eq_(temp_3_0, temp_3_1)) by {
		lemma_mul_assoc(mul_(b, a), d, a);
	}
	let temp_4_0 = (mul_((mod_((mul_(c, d)), m)), (add_((mod_(c, m)), b))));
	let temp_4_1 = (mul_((mod_((mul_(c, d)), m)), (add_((mod_((add_(c, (mul_((mul_((mod_((mul_((mod_(d, m)), a)), m)), (mod_((mul_(a, (mod_(c, m)))), m)))), m)))), m)), b))));
	assert(eq_(temp_4_0, temp_4_1)) by {
		cong_mul_(mod_(mul_(c, d), m), add_(mod_(c, m), b), mod_(mul_(c, d), m), add_(mod_(add_(c, mul_(mul_(mod_(mul_(mod_(d, m), a), m), mod_(mul_(a, mod_(c, m)), m)), m)), m), b));
		lemma_mod_mul_vanish(c, mul_(mod_(mul_(mod_(d, m), a), m), mod_(mul_(a, mod_(c, m)), m)), m);
		lemma_eq_ref(mod_(mul_(c, d), m));
		cong_add_(mod_(c, m), b, mod_(add_(c, mul_(mul_(mod_(mul_(mod_(d, m), a), m), mod_(mul_(a, mod_(c, m)), m)), m)), m), b);
		lemma_eq_ref(b);
	}
	let temp_5_0 = (mul_((mul_(d, a)), (mod_((sub_(a, c)), m))));
	let temp_5_1 = (mul_(d, (mul_(a, (mod_((sub_(a, c)), m))))));
	assert(eq_(temp_5_0, temp_5_1)) by {
		lemma_mul_assoc(d, a, mod_(sub_(a, c), m));
		lemma_eq_sym(temp_5_1, temp_5_0);
	}
	let temp_6_0 = (mod_((mul_((mul_(d, b)), c)), m));
	let temp_6_1 = (mod_((sub_((mul_((mul_(d, b)), c)), (mul_((mul_((add_(c, (mod_(a, m)))), (mod_((mul_(b, (mod_(a, m)))), m)))), m)))), m));
	assert(eq_(temp_6_0, temp_6_1)) by {
		lemma_mod_mul_vanish(mul_(mul_(d, b), c), mul_(add_(c, mod_(a, m)), mod_(mul_(b, mod_(a, m)), m)), m);
	}
	let temp_7_0 = (mul_((mul_(d, b)), (mul_(b, d))));
	let temp_7_1 = (mul_((mul_(d, b)), (mul_(d, b))));
	assert(eq_(temp_7_0, temp_7_1)) by {
		cong_mul_(mul_(d, b), mul_(b, d), mul_(d, b), mul_(d, b));
		lemma_mul_comm(b, d);
		lemma_eq_ref(mul_(d, b));
	}
	let temp_8_0 = (mul_((mul_((mod_(b, m)), d)), (mul_(c, c))));
	let temp_8_1 = (mul_((mul_((mod_((add_((mul_((mul_((add_(b, b)), (mul_(b, (mod_(d, m)))))), m)), b)), m)), d)), (mul_(c, c))));
	assert(eq_(temp_8_0, temp_8_1)) by {
		lemma_mul_comm(c, c);
		lemma_mod_mul_vanish(b, mul_(add_(b, b), mul_(b, mod_(d, m))), m);
		cong_mul_(mul_(mod_(b, m), d), mul_(c, c), mul_(mod_(add_(mul_(mul_(add_(b, b), mul_(b, mod_(d, m))), m), b), m), d), mul_(c, c));
		cong_mul_(mod_(b, m), d, mod_(add_(mul_(mul_(add_(b, b), mul_(b, mod_(d, m))), m), b), m), d);
		lemma_eq_ref(d);
	}
	let temp_9_0 = (mul_((mul_(a, d)), (mod_((mul_(d, b)), m))));
	let temp_9_1 = (mul_(a, (mul_(d, (mod_((mul_(d, b)), m))))));
	assert(eq_(temp_9_0, temp_9_1)) by {
		lemma_mul_assoc(a, d, mod_(mul_(d, b), m));
		lemma_eq_sym(temp_9_1, temp_9_0);
	}
	let temp_10_0 = (mul_((mul_(d, c)), (mul_(as_elem(52), c))));
	let temp_10_1 = (mul_((mul_(d, c)), (mul_(c, as_elem(52)))));
	assert(eq_(temp_10_0, temp_10_1)) by {
		cong_mul_(mul_(d, c), mul_(as_elem(52), c), mul_(d, c), mul_(c, as_elem(52)));
		lemma_mul_comm(as_elem(52), c);
		lemma_eq_ref(mul_(d, c));
	}
	let temp_11_0 = (mul_((mul_(b, a)), (mod_((mul_(a, b)), m))));
	let temp_11_1 = (mul_((mul_(b, a)), (mod_((sub_((mul_(a, b)), (mul_((mul_((mul_(b, as_elem(71))), (mul_(a, b)))), m)))), m))));
	assert(eq_(temp_11_0, temp_11_1)) by {
		lemma_mod_mul_vanish(mul_(a, b), mul_(mul_(b, as_elem(71)), mul_(a, b)), m);
		cong_mul_(mul_(b, a), mod_(mul_(a, b), m), mul_(b, a), mod_(sub_(mul_(a, b), mul_(mul_(mul_(b, as_elem(71)), mul_(a, b)), m)), m));
		lemma_eq_ref(mul_(b, a));
	}
	let temp_12_0 = (add_((sub_(d, b)), (mul_(b, d))));
	let temp_12_1 = (add_((mul_(b, d)), (sub_(d, b))));
	assert(eq_(temp_12_0, temp_12_1)) by {
		lemma_add_comm(sub_(d, b), mul_(b, d));
	}
	let temp_13_0 = (mul_((mul_(a, a)), (mul_(b, a))));
	let temp_13_1 = (mul_((mul_(a, a)), (mul_(a, b))));
	assert(eq_(temp_13_0, temp_13_1)) by {
		cong_mul_(mul_(a, a), mul_(b, a), mul_(a, a), mul_(a, b));
		lemma_mul_comm(a, a);
		lemma_mul_comm(b, a);
	}
	let temp_14_0 = (mul_((mul_((mod_(d, m)), c)), (mul_(d, c))));
	let temp_14_1 = (mul_((mul_((mod_((add_(d, (mul_((sub_((mul_(d, d)), (mod_((mul_(b, a)), m)))), m)))), m)), c)), (mul_(d, c))));
	assert(eq_(temp_14_0, temp_14_1)) by {
		lemma_mod_mul_vanish(d, sub_(mul_(d, d), mod_(mul_(b, a), m)), m);
		cong_mul_(mul_(mod_(d, m), c), mul_(d, c), mul_(mod_(add_(d, mul_(sub_(mul_(d, d), mod_(mul_(b, a), m)), m)), m), c), mul_(d, c));
		lemma_eq_ref(c);
		cong_mul_(mod_(d, m), c, mod_(add_(d, mul_(sub_(mul_(d, d), mod_(mul_(b, a), m)), m)), m), c);
		lemma_eq_ref(mul_(d, c));
	}
	let temp_15_0 = (mul_(d, (mul_(d, b))));
	let temp_15_1 = (mul_((mul_(d, d)), b));
	assert(eq_(temp_15_0, temp_15_1)) by {
		lemma_mul_assoc(d, d, b);
	}
	let temp_16_0 = (mul_((mul_(a, b)), (mul_(c, (mod_(as_elem(73), m))))));
	let temp_16_1 = (mul_((mul_(c, (mod_(as_elem(73), m)))), (mul_(a, b))));
	assert(eq_(temp_16_0, temp_16_1)) by {
		lemma_mul_comm(mul_(a, b), mul_(c, mod_(as_elem(73), m)));
	}
	let temp_17_0 = (sub_((mul_(a, c)), (mul_(d, b))));
	let temp_17_1 = (sub_((mul_(c, a)), (mul_(d, b))));
	assert(eq_(temp_17_0, temp_17_1)) by {
		cong_sub_(mul_(a, c), mul_(d, b), mul_(c, a), mul_(d, b));
		lemma_mul_comm(a, c);
		lemma_eq_ref(mul_(d, b));
	}
	let temp_18_0 = (mul_((mul_(c, d)), (mul_(c, c))));
	let temp_18_1 = (mul_((mul_((mul_(c, d)), c)), c));
	assert(eq_(temp_18_0, temp_18_1)) by {
		lemma_mul_assoc(mul_(c, d), c, c);
	}
	let temp_19_0 = (mul_((mul_(as_elem(15), d)), (mul_(a, a))));
	let temp_19_1 = (mul_((mul_(a, a)), (mul_(as_elem(15), d))));
	assert(eq_(temp_19_0, temp_19_1)) by {
		lemma_mul_comm(mul_(as_elem(15), d), mul_(a, a));
	}
	let temp_20_0 = (sub_((mul_(b, c)), (mul_(d, d))));
	let temp_20_1 = (sub_((mul_(c, b)), (mul_(d, d))));
	assert(eq_(temp_20_0, temp_20_1)) by {
		cong_sub_(mul_(b, c), mul_(d, d), mul_(c, b), mul_(d, d));
		lemma_mul_comm(b, c);
		lemma_mul_comm(d, d);
	}
	let temp_21_0 = (mul_(b, (mul_(c, a))));
	let temp_21_1 = (mul_((mul_(b, c)), a));
	assert(eq_(temp_21_0, temp_21_1)) by {
		lemma_mul_assoc(b, c, a);
	}
	let temp_22_0 = (mul_((mul_(b, b)), (mod_((sub_(a, b)), m))));
	let temp_22_1 = (mul_((mul_(b, b)), (mod_((sub_((mod_(a, m)), b)), m))));
	assert(eq_(temp_22_0, temp_22_1)) by {
		cong_mul_(mul_(b, b), mod_(sub_(a, b), m), mul_(b, b), mod_(sub_(mod_(a, m), b), m));
		lemma_mod_sub_noop(a, b, m);
		lemma_eq_ref(mul_(b, b));
	}
	let temp_23_0 = (mod_((mul_(a, (mul_(c, c)))), m));
	let temp_23_1 = (mod_((mul_(a, (mul_(c, c)))), m));
	assert(eq_(temp_23_0, temp_23_1)) by {
		lemma_eq_ref(temp_23_0);
	}
	let temp_24_0 = (mod_((mul_((mul_(c, d)), (mul_(b, b)))), m));
	let temp_24_1 = (mod_((add_((mul_((mul_((mul_(d, c)), (mul_(b, a)))), m)), (mul_((mul_(c, d)), (mul_(b, b)))))), m));
	assert(eq_(temp_24_0, temp_24_1)) by {
		lemma_mod_mul_vanish(mul_(mul_(c, d), mul_(b, b)), mul_(mul_(d, c), mul_(b, a)), m);
	}
	let temp_25_0 = (mul_((mul_(a, c)), (mul_(b, d))));
	let temp_25_1 = (mul_((mul_(a, c)), (mul_(d, b))));
	assert(eq_(temp_25_0, temp_25_1)) by {
		cong_mul_(mul_(a, c), mul_(b, d), mul_(a, c), mul_(d, b));
		lemma_mul_comm(b, d);
		lemma_eq_ref(mul_(a, c));
	}
	let temp_26_0 = (sub_((mul_(a, a)), (mul_(c, as_elem(24)))));
	let temp_26_1 = (sub_((mul_(a, a)), (mul_(as_elem(24), c))));
	assert(eq_(temp_26_0, temp_26_1)) by {
		cong_sub_(mul_(a, a), mul_(c, as_elem(24)), mul_(a, a), mul_(as_elem(24), c));
		lemma_mul_comm(c, as_elem(24));
		lemma_eq_ref(mul_(a, a));
	}
	let temp_27_0 = (mul_((mul_(a, c)), (mul_(a, d))));
	let temp_27_1 = (mul_((mul_((mul_(a, c)), a)), d));
	assert(eq_(temp_27_0, temp_27_1)) by {
		lemma_mul_assoc(mul_(a, c), a, d);
	}
	let temp_28_0 = (mul_((mul_(c, a)), (mod_((mul_(d, d)), m))));
	let temp_28_1 = (mul_((mod_((mul_(d, d)), m)), (mul_(c, a))));
	assert(eq_(temp_28_0, temp_28_1)) by {
		lemma_mul_comm(mul_(c, a), mod_(mul_(d, d), m));
	}
	let temp_29_0 = (add_((mul_(b, c)), (mul_(b, c))));
	let temp_29_1 = (mul_((add_(b, b)), c));
	assert(eq_(temp_29_0, temp_29_1)) by {
		lemma_eq_sym(temp_29_1, temp_29_0);
		lemma_mul_dist(b, b, c);
	}
	let temp_30_0 = (add_((sub_(a, d)), (mul_(c, d))));
	let temp_30_1 = (add_((mul_(c, d)), (sub_(a, d))));
	assert(eq_(temp_30_0, temp_30_1)) by {
		lemma_add_comm(sub_(a, d), mul_(c, d));
	}
	let temp_31_0 = (mod_((mul_((mul_(c, a)), (mul_(b, a)))), m));
	let temp_31_1 = (mod_((mul_((mul_((mul_(c, a)), b)), a)), m));
	assert(eq_(temp_31_0, temp_31_1)) by {
		lemma_mul_assoc(mul_(c, a), b, a);
		cong_mod_(mul_(mul_(c, a), mul_(b, a)), m, mul_(mul_(mul_(c, a), b), a), m);
		lemma_eq_ref(m);
	}
	let temp_32_0 = (mul_((add_(b, a)), (mul_(c, d))));
	let temp_32_1 = (mul_((mul_((add_(b, a)), c)), d));
	assert(eq_(temp_32_0, temp_32_1)) by {
		lemma_mul_assoc(add_(b, a), c, d);
	}
	let temp_33_0 = (mul_((mul_(b, as_elem(87))), (mul_(c, b))));
	let temp_33_1 = (mul_(b, (mul_(as_elem(87), (mul_(c, b))))));
	assert(eq_(temp_33_0, temp_33_1)) by {
		lemma_eq_sym(temp_33_1, temp_33_0);
		lemma_mul_assoc(b, as_elem(87), mul_(c, b));
	}
	let temp_34_0 = (sub_((mul_(d, a)), (sub_(b, (mod_(c, m))))));
	let temp_34_1 = (sub_((mul_(a, d)), (sub_(b, (mod_(c, m))))));
	assert(eq_(temp_34_0, temp_34_1)) by {
		lemma_mul_comm(d, a);
		cong_sub_(mul_(d, a), sub_(b, mod_(c, m)), mul_(a, d), sub_(b, mod_(c, m)));
		lemma_eq_ref(sub_(b, mod_(c, m)));
	}
	let temp_35_0 = (mul_((mul_(b, d)), (add_(a, (mod_(a, m))))));
	let temp_35_1 = (mul_(b, (mul_(d, (add_(a, (mod_(a, m))))))));
	assert(eq_(temp_35_0, temp_35_1)) by {
		lemma_mul_assoc(b, d, add_(a, mod_(a, m)));
		lemma_eq_sym(temp_35_1, temp_35_0);
	}
	let temp_36_0 = (mul_((mul_((mod_(b, m)), b)), (add_(c, b))));
	let temp_36_1 = (mul_((mul_((mod_(b, m)), b)), (add_(b, c))));
	assert(eq_(temp_36_0, temp_36_1)) by {
		lemma_add_comm(b, c);
		cong_mul_(mul_(mod_(b, m), b), add_(c, b), mul_(mod_(b, m), b), add_(b, c));
		lemma_eq_sym(add_(b, c), add_(c, b));
		lemma_eq_ref(mul_(mod_(b, m), b));
	}
	let temp_37_0 = (mul_((mul_(c, d)), (mul_(c, a))));
	let temp_37_1 = (mul_((mul_(d, c)), (mul_(c, a))));
	assert(eq_(temp_37_0, temp_37_1)) by {
		cong_mul_(mul_(c, d), mul_(c, a), mul_(d, c), mul_(c, a));
		lemma_mul_comm(c, d);
		lemma_eq_ref(mul_(c, a));
	}
	let temp_38_0 = (add_((mul_(a, c)), (mod_((mul_(a, a)), m))));
	let temp_38_1 = (add_((mul_(a, c)), (mod_((add_((mul_(a, a)), (mul_((sub_((mul_(a, b)), (mul_(d, c)))), m)))), m))));
	assert(eq_(temp_38_0, temp_38_1)) by {
		lemma_mod_mul_vanish(mul_(a, a), sub_(mul_(a, b), mul_(d, c)), m);
		cong_add_(mul_(a, c), mod_(mul_(a, a), m), mul_(a, c), mod_(add_(mul_(a, a), mul_(sub_(mul_(a, b), mul_(d, c)), m)), m));
		lemma_eq_ref(mul_(a, c));
	}
	let temp_39_0 = (mod_((mul_((mul_(a, (mod_(b, m)))), (mul_(b, c)))), m));
	let temp_39_1 = (mod_((mul_((mul_(b, c)), (mul_(a, (mod_(b, m)))))), m));
	assert(eq_(temp_39_0, temp_39_1)) by {
		lemma_mul_comm(mul_(a, mod_(b, m)), mul_(b, c));
		cong_mod_(mul_(mul_(a, mod_(b, m)), mul_(b, c)), m, mul_(mul_(b, c), mul_(a, mod_(b, m))), m);
		lemma_eq_ref(m);
	}
	let temp_40_0 = (add_((mul_(b, d)), (mod_((mul_(a, c)), m))));
	let temp_40_1 = (add_((mul_(b, d)), (mod_((add_((mul_((mul_((mul_(c, a)), (mul_(b, c)))), m)), (mul_(a, c)))), m))));
	assert(eq_(temp_40_0, temp_40_1)) by {
		lemma_mod_mul_vanish(mul_(a, c), mul_(mul_(c, a), mul_(b, c)), m);
		cong_add_(mul_(b, d), mod_(mul_(a, c), m), mul_(b, d), mod_(add_(mul_(mul_(mul_(c, a), mul_(b, c)), m), mul_(a, c)), m));
		lemma_eq_ref(mul_(b, d));
	}
	let temp_41_0 = (mul_((sub_(c, d)), (mul_(a, a))));
	let temp_41_1 = (mul_((mul_((sub_(c, d)), a)), a));
	assert(eq_(temp_41_0, temp_41_1)) by {
		lemma_mul_assoc(sub_(c, d), a, a);
	}
	let temp_42_0 = (mul_((mul_(a, b)), (mul_(d, b))));
	let temp_42_1 = (mul_((mul_((mul_(a, b)), d)), b));
	assert(eq_(temp_42_0, temp_42_1)) by {
		lemma_mul_assoc(mul_(a, b), d, b);
	}
	let temp_43_0 = (mul_((mul_(c, b)), (mul_(c, a))));
	let temp_43_1 = (mul_((mul_(b, c)), (mul_(c, a))));
	assert(eq_(temp_43_0, temp_43_1)) by {
		cong_mul_(mul_(c, b), mul_(c, a), mul_(b, c), mul_(c, a));
		lemma_mul_comm(c, b);
		lemma_eq_ref(mul_(c, a));
	}
	let temp_44_0 = (mul_((mul_(c, d)), (mul_(b, (mod_(a, m))))));
	let temp_44_1 = (mul_((mul_((mul_(c, d)), b)), (mod_(a, m))));
	assert(eq_(temp_44_0, temp_44_1)) by {
		lemma_mul_assoc(mul_(c, d), b, mod_(a, m));
	}
	let temp_45_0 = (mul_((mul_(c, (mod_(d, m)))), (mul_(c, b))));
	let temp_45_1 = (mul_((mul_(c, b)), (mul_(c, (mod_(d, m))))));
	assert(eq_(temp_45_0, temp_45_1)) by {
		lemma_mul_comm(mul_(c, mod_(d, m)), mul_(c, b));
	}
	let temp_46_0 = (mul_((mul_(a, a)), (mul_(d, a))));
	let temp_46_1 = (mul_((mul_((mul_(a, a)), d)), a));
	assert(eq_(temp_46_0, temp_46_1)) by {
		lemma_mul_assoc(mul_(a, a), d, a);
	}
	let temp_47_0 = (mul_((mul_(a, a)), (mod_((sub_(d, a)), m))));
	let temp_47_1 = (mul_(a, (mul_(a, (mod_((sub_(d, a)), m))))));
	assert(eq_(temp_47_0, temp_47_1)) by {
		lemma_eq_sym(temp_47_1, temp_47_0);
		lemma_mul_assoc(a, a, mod_(sub_(d, a), m));
	}
	let temp_48_0 = (add_((mul_(c, a)), (mul_(b, b))));
	let temp_48_1 = (add_((mul_(c, a)), (mul_(b, b))));
	assert(eq_(temp_48_0, temp_48_1)) by {
		lemma_eq_ref(temp_48_0);
	}
	let temp_49_0 = (mul_((sub_(b, d)), (mod_((mul_(b, d)), m))));
	let temp_49_1 = (sub_((mul_(b, (mod_((mul_(b, d)), m)))), (mul_(d, (mod_((mul_(b, d)), m))))));
	assert(eq_(temp_49_0, temp_49_1)) by {
		lemma_mul_dist(mod_(mul_(b, d), m), b, d);
	}
	let temp_50_0 = (mul_((mul_(b, (mod_(c, m)))), (mul_((mod_(a, m)), b))));
	let temp_50_1 = (mul_((mul_(b, (mod_(c, m)))), (mul_((mod_((add_(a, (mul_((mod_((mul_((mul_(a, d)), (mul_(b, c)))), m)), m)))), m)), b))));
	assert(eq_(temp_50_0, temp_50_1)) by {
		lemma_eq_ref(mul_(b, mod_(c, m)));
		cong_mul_(mod_(a, m), b, mod_(add_(a, mul_(mod_(mul_(mul_(a, d), mul_(b, c)), m), m)), m), b);
		lemma_mod_mul_vanish(a, mod_(mul_(mul_(a, d), mul_(b, c)), m), m);
		cong_mul_(mul_(b, mod_(c, m)), mul_(mod_(a, m), b), mul_(b, mod_(c, m)), mul_(mod_(add_(a, mul_(mod_(mul_(mul_(a, d), mul_(b, c)), m), m)), m), b));
		lemma_eq_ref(b);
	}
	let temp_51_0 = (add_((mul_(d, b)), (mul_(a, d))));
	let temp_51_1 = (add_((mul_(d, b)), (mul_(d, a))));
	assert(eq_(temp_51_0, temp_51_1)) by {
		cong_add_(mul_(d, b), mul_(a, d), mul_(d, b), mul_(d, a));
		lemma_mul_comm(a, d);
		lemma_eq_ref(mul_(d, b));
	}
	let temp_52_0 = (mul_((mul_(b, d)), (mul_(b, c))));
	let temp_52_1 = (mul_((mul_(d, b)), (mul_(b, c))));
	assert(eq_(temp_52_0, temp_52_1)) by {
		cong_mul_(mul_(b, d), mul_(b, c), mul_(d, b), mul_(b, c));
		lemma_mul_comm(b, d);
		lemma_eq_ref(mul_(b, c));
	}
	let temp_53_0 = (sub_((add_(b, d)), (mul_(c, (mod_(c, m))))));
	let temp_53_1 = (sub_((add_(b, d)), (mul_(c, (mod_((add_((mul_((mul_((mul_(d, d)), (mul_(b, a)))), m)), c)), m))))));
	assert(eq_(temp_53_0, temp_53_1)) by {
		lemma_mod_mul_vanish(c, mul_(mul_(d, d), mul_(b, a)), m);
		cong_sub_(add_(b, d), mul_(c, mod_(c, m)), add_(b, d), mul_(c, mod_(add_(mul_(mul_(mul_(d, d), mul_(b, a)), m), c), m)));
		lemma_eq_ref(c);
		lemma_eq_ref(add_(b, d));
		cong_mul_(c, mod_(c, m), c, mod_(add_(mul_(mul_(mul_(d, d), mul_(b, a)), m), c), m));
	}
	let temp_54_0 = (mul_((mul_(b, (mod_(a, m)))), (mul_((mod_(c, m)), as_elem(68)))));
	let temp_54_1 = (mul_((mul_((mul_(b, (mod_(a, m)))), (mod_(c, m)))), as_elem(68)));
	assert(eq_(temp_54_0, temp_54_1)) by {
		lemma_mul_assoc(mul_(b, mod_(a, m)), mod_(c, m), as_elem(68));
	}
	let temp_55_0 = (mul_((add_(c, b)), (mul_(a, (mod_(c, m))))));
	let temp_55_1 = (mul_((add_(c, b)), (mul_(a, (mod_((sub_(c, (mul_((add_((add_(c, a)), (mul_(c, b)))), m)))), m))))));
	assert(eq_(temp_55_0, temp_55_1)) by {
		lemma_mod_mul_vanish(c, add_(add_(c, a), mul_(c, b)), m);
		cong_mul_(add_(c, b), mul_(a, mod_(c, m)), add_(c, b), mul_(a, mod_(sub_(c, mul_(add_(add_(c, a), mul_(c, b)), m)), m)));
		cong_mul_(a, mod_(c, m), a, mod_(sub_(c, mul_(add_(add_(c, a), mul_(c, b)), m)), m));
		lemma_eq_ref(a);
		lemma_eq_ref(add_(c, b));
	}
	let temp_56_0 = (mul_((mul_(a, d)), d));
	let temp_56_1 = (mul_(a, (mul_(d, d))));
	assert(eq_(temp_56_0, temp_56_1)) by {
		lemma_eq_sym(temp_56_1, temp_56_0);
		lemma_mul_assoc(a, d, d);
	}
	let temp_57_0 = (add_(d, (mul_(a, d))));
	let temp_57_1 = (add_((mul_(a, d)), d));
	assert(eq_(temp_57_0, temp_57_1)) by {
		lemma_add_comm(d, mul_(a, d));
	}
	let temp_58_0 = (mul_((mul_(b, (mod_(a, m)))), (add_(c, c))));
	let temp_58_1 = (mul_((mul_(b, (mod_(a, m)))), (add_(c, c))));
	assert(eq_(temp_58_0, temp_58_1)) by {
		lemma_eq_ref(temp_58_0);
	}
	let temp_59_0 = (mul_((mul_(d, b)), (mod_(b, m))));
	let temp_59_1 = (mul_((mul_(d, b)), (mod_((add_((mul_((sub_((mul_(b, b)), (mul_(a, d)))), m)), b)), m))));
	assert(eq_(temp_59_0, temp_59_1)) by {
		lemma_mod_mul_vanish(b, sub_(mul_(b, b), mul_(a, d)), m);
		cong_mul_(mul_(d, b), mod_(b, m), mul_(d, b), mod_(add_(mul_(sub_(mul_(b, b), mul_(a, d)), m), b), m));
		lemma_eq_ref(mul_(d, b));
	}
	let temp_60_0 = (mul_((add_(c, d)), (mul_(b, d))));
	let temp_60_1 = (mul_((add_(d, c)), (mul_(b, d))));
	assert(eq_(temp_60_0, temp_60_1)) by {
		cong_mul_(add_(c, d), mul_(b, d), add_(d, c), mul_(b, d));
		lemma_add_comm(c, d);
		lemma_eq_ref(mul_(b, d));
	}
	let temp_61_0 = (mul_((mul_(b, c)), (mul_(d, a))));
	let temp_61_1 = (mul_((mul_(c, b)), (mul_(d, a))));
	assert(eq_(temp_61_0, temp_61_1)) by {
		cong_mul_(mul_(b, c), mul_(d, a), mul_(c, b), mul_(d, a));
		lemma_mul_comm(b, c);
		lemma_eq_ref(mul_(d, a));
	}
	let temp_62_0 = (mul_((mul_(a, c)), (mul_(a, b))));
	let temp_62_1 = (mul_((mul_(a, b)), (mul_(a, c))));
	assert(eq_(temp_62_0, temp_62_1)) by {
		lemma_mul_comm(mul_(a, c), mul_(a, b));
	}
	let temp_63_0 = (add_((mul_(b, d)), (mul_(a, b))));
	let temp_63_1 = (add_((mul_(d, b)), (mul_(a, b))));
	assert(eq_(temp_63_0, temp_63_1)) by {
		cong_add_(mul_(b, d), mul_(a, b), mul_(d, b), mul_(a, b));
		lemma_mul_comm(b, d);
		lemma_eq_ref(mul_(a, b));
	}
	let temp_64_0 = (mul_((mul_(a, b)), (mul_(b, d))));
	let temp_64_1 = (mul_((mul_((mul_(a, b)), b)), d));
	assert(eq_(temp_64_0, temp_64_1)) by {
		lemma_mul_assoc(mul_(a, b), b, d);
	}
	let temp_65_0 = (mul_((sub_(c, a)), (mul_(c, d))));
	let temp_65_1 = (sub_((mul_(c, (mul_(c, d)))), (mul_(a, (mul_(c, d))))));
	assert(eq_(temp_65_0, temp_65_1)) by {
		lemma_mul_dist(mul_(c, d), c, a);
	}
	let temp_66_0 = (mul_((mul_(c, b)), (mul_(a, c))));
	let temp_66_1 = (mul_(c, (mul_(b, (mul_(a, c))))));
	assert(eq_(temp_66_0, temp_66_1)) by {
		lemma_eq_sym(temp_66_1, temp_66_0);
		lemma_mul_assoc(c, b, mul_(a, c));
	}
	let temp_67_0 = (mul_((mul_(c, (mod_(a, m)))), (mul_(b, c))));
	let temp_67_1 = (mul_((mul_((mul_(c, (mod_(a, m)))), b)), c));
	assert(eq_(temp_67_0, temp_67_1)) by {
		lemma_mul_assoc(mul_(c, mod_(a, m)), b, c);
	}
	let temp_68_0 = (mul_((mul_(c, a)), (mul_(c, d))));
	let temp_68_1 = (mul_((mul_(a, c)), (mul_(c, d))));
	assert(eq_(temp_68_0, temp_68_1)) by {
		cong_mul_(mul_(c, a), mul_(c, d), mul_(a, c), mul_(c, d));
		lemma_mul_comm(c, a);
		lemma_eq_ref(mul_(c, d));
	}
	let temp_69_0 = (mul_((mod_((sub_(d, b)), m)), (mod_((mul_(b, (mod_(c, m)))), m))));
	let temp_69_1 = (mul_((mod_((sub_(d, b)), m)), (mod_((sub_((mul_(b, (mod_(c, m)))), (mul_((mul_((sub_(a, d)), (mul_(d, d)))), m)))), m))));
	assert(eq_(temp_69_0, temp_69_1)) by {
		lemma_mod_mul_vanish(mul_(b, mod_(c, m)), mul_(sub_(a, d), mul_(d, d)), m);
		cong_mul_(mod_(sub_(d, b), m), mod_(mul_(b, mod_(c, m)), m), mod_(sub_(d, b), m), mod_(sub_(mul_(b, mod_(c, m)), mul_(mul_(sub_(a, d), mul_(d, d)), m)), m));
		lemma_eq_ref(mod_(sub_(d, b), m));
	}
	let temp_70_0 = (mul_((mul_(c, d)), (mul_(a, a))));
	let temp_70_1 = (mul_((mul_((mul_(c, d)), a)), a));
	assert(eq_(temp_70_0, temp_70_1)) by {
		lemma_mul_assoc(mul_(c, d), a, a);
	}
	let temp_71_0 = (mul_((mul_(c, d)), (mul_(c, d))));
	let temp_71_1 = (mul_((mul_((mul_(c, d)), c)), d));
	assert(eq_(temp_71_0, temp_71_1)) by {
		lemma_mul_assoc(mul_(c, d), c, d);
	}
	let temp_72_0 = (mul_((mul_(b, a)), (mul_(a, c))));
	let temp_72_1 = (mul_((mul_((mul_(b, a)), a)), c));
	assert(eq_(temp_72_0, temp_72_1)) by {
		lemma_mul_assoc(mul_(b, a), a, c);
	}
	let temp_73_0 = (mul_((mul_(a, c)), (mul_(a, (mod_(c, m))))));
	let temp_73_1 = (mul_(a, (mul_(c, (mul_(a, (mod_(c, m))))))));
	assert(eq_(temp_73_0, temp_73_1)) by {
		lemma_eq_sym(temp_73_1, temp_73_0);
		lemma_mul_assoc(a, c, mul_(a, mod_(c, m)));
	}
	let temp_74_0 = (mod_((mul_((mul_(d, d)), (mul_(a, c)))), m));
	let temp_74_1 = (mod_((mul_((mul_(d, d)), (mul_(a, c)))), m));
	assert(eq_(temp_74_0, temp_74_1)) by {
		lemma_eq_ref(temp_74_0);
	}
	let temp_75_0 = (add_((mul_((mod_(c, m)), d)), (mul_(b, c))));
	let temp_75_1 = (add_((mul_((mod_((add_((mul_((mul_((mul_(a, b)), (mul_(b, c)))), m)), c)), m)), d)), (mul_(b, c))));
	assert(eq_(temp_75_0, temp_75_1)) by {
		lemma_mod_mul_vanish(c, mul_(mul_(a, b), mul_(b, c)), m);
		cong_add_(mul_(mod_(c, m), d), mul_(b, c), mul_(mod_(add_(mul_(mul_(mul_(a, b), mul_(b, c)), m), c), m), d), mul_(b, c));
		cong_mul_(mod_(c, m), d, mod_(add_(mul_(mul_(mul_(a, b), mul_(b, c)), m), c), m), d);
		lemma_eq_ref(mul_(b, c));
		lemma_eq_ref(d);
	}
	let temp_76_0 = (mul_((mod_((mul_(d, b)), m)), (mod_((mul_(b, c)), m))));
	let temp_76_1 = (mul_((mod_((mul_(d, b)), m)), (mod_((sub_((mul_(b, c)), (mul_((mul_((add_(c, b)), (mul_((mod_(a, m)), d)))), m)))), m))));
	assert(eq_(temp_76_0, temp_76_1)) by {
		lemma_mod_mul_vanish(mul_(b, c), mul_(add_(c, b), mul_(mod_(a, m), d)), m);
		cong_mul_(mod_(mul_(d, b), m), mod_(mul_(b, c), m), mod_(mul_(d, b), m), mod_(sub_(mul_(b, c), mul_(mul_(add_(c, b), mul_(mod_(a, m), d)), m)), m));
		lemma_eq_ref(mod_(mul_(d, b), m));
	}
	let temp_77_0 = (add_((mul_((mod_(a, m)), b)), (mul_(b, b))));
	let temp_77_1 = (add_((mul_(b, b)), (mul_((mod_(a, m)), b))));
	assert(eq_(temp_77_0, temp_77_1)) by {
		lemma_add_comm(mul_(mod_(a, m), b), mul_(b, b));
	}
	let temp_78_0 = (mul_((mod_((mul_(d, c)), m)), (mul_(a, c))));
	let temp_78_1 = (mul_((mul_(a, c)), (mod_((mul_(d, c)), m))));
	assert(eq_(temp_78_0, temp_78_1)) by {
		lemma_mul_comm(mod_(mul_(d, c), m), mul_(a, c));
	}
	let temp_79_0 = (mul_((mul_(a, b)), (mul_(a, b))));
	let temp_79_1 = (mul_((mul_(a, b)), (mul_(b, a))));
	assert(eq_(temp_79_0, temp_79_1)) by {
		cong_mul_(mul_(a, b), mul_(a, b), mul_(a, b), mul_(b, a));
		lemma_mul_comm(a, b);
		lemma_eq_ref(mul_(a, b));
	}
	let temp_80_0 = (sub_((add_(a, c)), (sub_(b, (mod_(c, m))))));
	let temp_80_1 = (sub_((add_(a, c)), (sub_(b, (mod_((sub_(c, (mul_((mul_((sub_(d, b)), (mul_(d, a)))), m)))), m))))));
	assert(eq_(temp_80_0, temp_80_1)) by {
		lemma_eq_ref(add_(a, c));
		cong_sub_(b, mod_(c, m), b, mod_(sub_(c, mul_(mul_(sub_(d, b), mul_(d, a)), m)), m));
		lemma_eq_ref(b);
		lemma_mod_mul_vanish(c, mul_(sub_(d, b), mul_(d, a)), m);
		cong_sub_(add_(a, c), sub_(b, mod_(c, m)), add_(a, c), sub_(b, mod_(sub_(c, mul_(mul_(sub_(d, b), mul_(d, a)), m)), m)));
	}
	let temp_81_0 = (mul_((mul_((mod_(a, m)), (mod_(c, m)))), (sub_(b, c))));
	let temp_81_1 = (mul_((mul_((mod_((add_((mul_((mul_((mul_(b, d)), (add_(d, d)))), m)), a)), m)), (mod_(c, m)))), (sub_(b, c))));
	assert(eq_(temp_81_0, temp_81_1)) by {
		lemma_mod_mul_vanish(a, mul_(mul_(b, d), add_(d, d)), m);
		cong_mul_(mul_(mod_(a, m), mod_(c, m)), sub_(b, c), mul_(mod_(add_(mul_(mul_(mul_(b, d), add_(d, d)), m), a), m), mod_(c, m)), sub_(b, c));
		lemma_eq_ref(mod_(c, m));
		cong_mul_(mod_(a, m), mod_(c, m), mod_(add_(mul_(mul_(mul_(b, d), add_(d, d)), m), a), m), mod_(c, m));
		lemma_eq_ref(sub_(b, c));
	}
	let temp_82_0 = (sub_((mul_((mod_(b, m)), c)), (mul_(b, d))));
	let temp_82_1 = (sub_((mul_(c, (mod_(b, m)))), (mul_(b, d))));
	assert(eq_(temp_82_0, temp_82_1)) by {
		lemma_mul_comm(mod_(b, m), c);
		cong_sub_(mul_(mod_(b, m), c), mul_(b, d), mul_(c, mod_(b, m)), mul_(b, d));
		lemma_eq_ref(mul_(b, d));
	}
	let temp_83_0 = (mul_((mul_(as_elem(58), b)), (mul_(b, d))));
	let temp_83_1 = (mul_((mul_(as_elem(58), b)), (mul_(d, b))));
	assert(eq_(temp_83_0, temp_83_1)) by {
		cong_mul_(mul_(as_elem(58), b), mul_(b, d), mul_(as_elem(58), b), mul_(d, b));
		lemma_mul_comm(b, d);
		lemma_eq_ref(mul_(as_elem(58), b));
	}
	let temp_84_0 = (mul_((sub_((mod_(b, m)), b)), (mul_(d, d))));
	let temp_84_1 = (mul_((mul_((sub_((mod_(b, m)), b)), d)), d));
	assert(eq_(temp_84_0, temp_84_1)) by {
		lemma_mul_assoc(sub_(mod_(b, m), b), d, d);
	}
	let temp_85_0 = (mul_((add_(a, d)), (mul_(d, c))));
	let temp_85_1 = (mul_((add_(a, d)), (mul_(c, d))));
	assert(eq_(temp_85_0, temp_85_1)) by {
		cong_mul_(add_(a, d), mul_(d, c), add_(a, d), mul_(c, d));
		lemma_mul_comm(d, c);
		lemma_eq_ref(add_(a, d));
	}
	let temp_86_0 = (mul_((mod_((mul_(a, c)), m)), (mul_(a, a))));
	let temp_86_1 = (mul_((mul_((mod_((mul_(a, c)), m)), a)), a));
	assert(eq_(temp_86_0, temp_86_1)) by {
		lemma_mul_assoc(mod_(mul_(a, c), m), a, a);
	}
	let temp_87_0 = (mul_((mul_(c, b)), (mod_((mul_(b, a)), m))));
	let temp_87_1 = (mul_(c, (mul_(b, (mod_((mul_(b, a)), m))))));
	assert(eq_(temp_87_0, temp_87_1)) by {
		lemma_mul_assoc(c, b, mod_(mul_(b, a), m));
		lemma_eq_sym(temp_87_1, temp_87_0);
	}
	let temp_88_0 = (add_((mul_(c, d)), (mod_((mul_(a, a)), m))));
	let temp_88_1 = (add_((mod_((mul_(a, a)), m)), (mul_(c, d))));
	assert(eq_(temp_88_0, temp_88_1)) by {
		lemma_add_comm(mul_(c, d), mod_(mul_(a, a), m));
	}
	let temp_89_0 = (mod_((mul_((mul_(d, d)), (mul_(d, a)))), m));
	let temp_89_1 = (mod_((sub_((mul_((mul_(d, d)), (mul_(d, a)))), (mul_((mul_((mul_(b, d)), (mul_(b, c)))), m)))), m));
	assert(eq_(temp_89_0, temp_89_1)) by {
		lemma_mod_mul_vanish(mul_(mul_(d, d), mul_(d, a)), mul_(mul_(b, d), mul_(b, c)), m);
	}
	let temp_90_0 = (mul_((mod_((mul_(a, c)), m)), (mul_(b, b))));
	let temp_90_1 = (mul_((mod_((add_((mul_(a, c)), (mul_((mul_((mod_((mul_(c, c)), m)), (mul_(d, d)))), m)))), m)), (mul_(b, b))));
	assert(eq_(temp_90_0, temp_90_1)) by {
		lemma_mul_comm(b, b);
		lemma_mod_mul_vanish(mul_(a, c), mul_(mod_(mul_(c, c), m), mul_(d, d)), m);
		cong_mul_(mod_(mul_(a, c), m), mul_(b, b), mod_(add_(mul_(a, c), mul_(mul_(mod_(mul_(c, c), m), mul_(d, d)), m)), m), mul_(b, b));
	}
	let temp_91_0 = (mul_((mul_(a, b)), (mul_(c, a))));
	let temp_91_1 = (mul_((mul_(b, a)), (mul_(c, a))));
	assert(eq_(temp_91_0, temp_91_1)) by {
		cong_mul_(mul_(a, b), mul_(c, a), mul_(b, a), mul_(c, a));
		lemma_mul_comm(a, b);
		lemma_eq_ref(mul_(c, a));
	}
	let temp_92_0 = (mul_((mod_((mul_(c, as_elem(51))), m)), (mul_(d, d))));
	let temp_92_1 = (mul_((mod_((mul_(c, as_elem(51))), m)), (mul_(d, d))));
	assert(eq_(temp_92_0, temp_92_1)) by {
		lemma_eq_ref(temp_92_0);
	}
	let temp_93_0 = (mul_((mul_(b, d)), (mul_(a, c))));
	let temp_93_1 = (mul_(b, (mul_(d, (mul_(a, c))))));
	assert(eq_(temp_93_0, temp_93_1)) by {
		lemma_eq_sym(temp_93_1, temp_93_0);
		lemma_mul_assoc(b, d, mul_(a, c));
	}
	let temp_94_0 = (mul_((mul_(b, a)), (mul_(b, (mod_(d, m))))));
	let temp_94_1 = (mul_(b, (mul_(a, (mul_(b, (mod_(d, m))))))));
	assert(eq_(temp_94_0, temp_94_1)) by {
		lemma_mul_assoc(b, a, mul_(b, mod_(d, m)));
		lemma_eq_sym(temp_94_1, temp_94_0);
	}
	let temp_95_0 = (add_((mul_(b, (mod_(d, m)))), (mul_(c, c))));
	let temp_95_1 = (add_((mul_(c, c)), (mul_(b, (mod_(d, m))))));
	assert(eq_(temp_95_0, temp_95_1)) by {
		lemma_add_comm(mul_(b, mod_(d, m)), mul_(c, c));
	}
	let temp_96_0 = (mul_((sub_(c, c)), (mul_(d, (mod_(d, m))))));
	let temp_96_1 = (mul_((sub_(c, c)), (mul_(d, (mod_((add_((mul_((sub_((mul_(b, a)), (mod_((mul_((mod_(c, m)), c)), m)))), m)), d)), m))))));
	assert(eq_(temp_96_0, temp_96_1)) by {
		lemma_mod_mul_vanish(d, sub_(mul_(b, a), mod_(mul_(mod_(c, m), c), m)), m);
		cong_mul_(sub_(c, c), mul_(d, mod_(d, m)), sub_(c, c), mul_(d, mod_(add_(mul_(sub_(mul_(b, a), mod_(mul_(mod_(c, m), c), m)), m), d), m)));
		lemma_eq_ref(d);
		cong_mul_(d, mod_(d, m), d, mod_(add_(mul_(sub_(mul_(b, a), mod_(mul_(mod_(c, m), c), m)), m), d), m));
		lemma_eq_ref(sub_(c, c));
	}
	let temp_97_0 = (mul_((mul_((mod_(b, m)), c)), (mul_(b, (mod_(d, m))))));
	let temp_97_1 = (mul_((mul_((mod_((add_((mul_((mul_((mul_(d, d)), (mul_(c, a)))), m)), b)), m)), c)), (mul_(b, (mod_(d, m))))));
	assert(eq_(temp_97_0, temp_97_1)) by {
		lemma_mod_mul_vanish(b, mul_(mul_(d, d), mul_(c, a)), m);
		cong_mul_(mul_(mod_(b, m), c), mul_(b, mod_(d, m)), mul_(mod_(add_(mul_(mul_(mul_(d, d), mul_(c, a)), m), b), m), c), mul_(b, mod_(d, m)));
		lemma_eq_ref(c);
		cong_mul_(mod_(b, m), c, mod_(add_(mul_(mul_(mul_(d, d), mul_(c, a)), m), b), m), c);
		lemma_eq_ref(mul_(b, mod_(d, m)));
	}
	let temp_98_0 = (sub_((sub_(b, c)), (mod_((mul_(c, b)), m))));
	let temp_98_1 = (sub_((sub_(b, c)), (mod_((sub_((mul_(c, b)), (mul_((mul_((sub_(d, a)), (mod_((add_(a, a)), m)))), m)))), m))));
	assert(eq_(temp_98_0, temp_98_1)) by {
		lemma_mod_mul_vanish(mul_(c, b), mul_(sub_(d, a), mod_(add_(a, a), m)), m);
		cong_sub_(sub_(b, c), mod_(mul_(c, b), m), sub_(b, c), mod_(sub_(mul_(c, b), mul_(mul_(sub_(d, a), mod_(add_(a, a), m)), m)), m));
		lemma_eq_ref(sub_(b, c));
	}
	let temp_99_0 = (mul_((mul_(a, c)), (mul_(a, c))));
	let temp_99_1 = (mul_((mul_(a, c)), (mul_(a, c))));
	assert(eq_(temp_99_0, temp_99_1)) by {
		lemma_eq_ref(temp_99_0);
	}
	let temp_100_0 = (mul_((mul_(c, d)), (mul_(c, d))));
	let temp_100_1 = (mul_((mul_(c, d)), (mul_(c, d))));
	assert(eq_(temp_100_0, temp_100_1)) by {
		lemma_eq_ref(temp_100_0);
	}
	let temp_101_0 = (add_((mul_(a, d)), (add_(a, d))));
	let temp_101_1 = (add_((mul_(d, a)), (add_(a, d))));
	assert(eq_(temp_101_0, temp_101_1)) by {
		cong_add_(mul_(a, d), add_(a, d), mul_(d, a), add_(a, d));
		lemma_mul_comm(a, d);
		lemma_eq_ref(add_(a, d));
	}
	let temp_102_0 = (sub_((mul_(b, a)), (add_(b, (mod_(d, m))))));
	let temp_102_1 = (sub_((mul_(b, a)), (add_((mod_(d, m)), b))));
	assert(eq_(temp_102_0, temp_102_1)) by {
		lemma_add_comm(b, mod_(d, m));
		cong_sub_(mul_(b, a), add_(b, mod_(d, m)), mul_(b, a), add_(mod_(d, m), b));
		lemma_eq_ref(mul_(b, a));
	}
	let temp_103_0 = (mul_((add_(d, c)), (mod_((mul_(c, c)), m))));
	let temp_103_1 = (mul_((add_(d, c)), (mod_((mul_(c, c)), m))));
	assert(eq_(temp_103_0, temp_103_1)) by {
		lemma_eq_ref(temp_103_0);
	}
	let temp_104_0 = (mul_((mul_((mod_(b, m)), d)), (mod_((mul_(d, d)), m))));
	let temp_104_1 = (mul_((mul_((mod_((add_(b, (mul_((mul_((sub_(a, a)), (mul_(d, d)))), m)))), m)), d)), (mod_((mul_(d, d)), m))));
	assert(eq_(temp_104_0, temp_104_1)) by {
		lemma_mod_mul_vanish(b, mul_(sub_(a, a), mul_(d, d)), m);
		cong_mul_(mul_(mod_(b, m), d), mod_(mul_(d, d), m), mul_(mod_(add_(b, mul_(mul_(sub_(a, a), mul_(d, d)), m)), m), d), mod_(mul_(d, d), m));
		lemma_eq_ref(d);
		cong_mul_(mod_(b, m), d, mod_(add_(b, mul_(mul_(sub_(a, a), mul_(d, d)), m)), m), d);
		lemma_eq_ref(mod_(mul_(d, d), m));
	}
	let temp_105_0 = (sub_((mul_(a, (mod_(d, m)))), (mul_(a, c))));
	let temp_105_1 = (sub_((mul_((mod_(d, m)), a)), (mul_(a, c))));
	assert(eq_(temp_105_0, temp_105_1)) by {
		lemma_mul_comm(a, mod_(d, m));
		cong_sub_(mul_(a, mod_(d, m)), mul_(a, c), mul_(mod_(d, m), a), mul_(a, c));
		lemma_eq_ref(mul_(a, c));
	}
	let temp_106_0 = (mul_((mul_(c, c)), (sub_(d, (mod_(as_elem(10), m))))));
	let temp_106_1 = (mul_(c, (mul_(c, (sub_(d, (mod_(as_elem(10), m))))))));
	assert(eq_(temp_106_0, temp_106_1)) by {
		lemma_mul_assoc(c, c, sub_(d, mod_(as_elem(10), m)));
		lemma_eq_sym(temp_106_1, temp_106_0);
	}
	let temp_107_0 = (mod_((mul_((mul_(a, as_elem(98))), (add_(d, b)))), m));
	let temp_107_1 = (mod_((mul_(a, (mul_(as_elem(98), (add_(d, b)))))), m));
	assert(eq_(temp_107_0, temp_107_1)) by {
		lemma_mul_assoc(a, as_elem(98), add_(d, b));
		cong_mod_(mul_(mul_(a, as_elem(98)), add_(d, b)), m, mul_(a, mul_(as_elem(98), add_(d, b))), m);
		lemma_eq_sym(mul_(a, mul_(as_elem(98), add_(d, b))), mul_(mul_(a, as_elem(98)), add_(d, b)));
		lemma_eq_ref(m);
	}
	let temp_108_0 = (add_((mul_(c, c)), (mul_(a, b))));
	let temp_108_1 = (add_((mul_(a, b)), (mul_(c, c))));
	assert(eq_(temp_108_0, temp_108_1)) by {
		lemma_add_comm(mul_(c, c), mul_(a, b));
	}
	let temp_109_0 = (mod_((mul_((add_(d, c)), (mul_(d, d)))), m));
	let temp_109_1 = (mod_((mul_((add_(c, d)), (mul_(d, d)))), m));
	assert(eq_(temp_109_0, temp_109_1)) by {
		lemma_mul_comm(d, d);
		lemma_add_comm(d, c);
		cong_mod_(mul_(add_(d, c), mul_(d, d)), m, mul_(add_(c, d), mul_(d, d)), m);
		cong_mul_(add_(d, c), mul_(d, d), add_(c, d), mul_(d, d));
		lemma_eq_ref(m);
	}
	let temp_110_0 = (mul_((mod_((mul_(a, d)), m)), (add_(b, b))));
	let temp_110_1 = (mul_((mod_((mul_(d, a)), m)), (add_(b, b))));
	assert(eq_(temp_110_0, temp_110_1)) by {
		cong_mod_(mul_(a, d), m, mul_(d, a), m);
		lemma_mul_comm(a, d);
		lemma_add_comm(b, b);
		cong_mul_(mod_(mul_(a, d), m), add_(b, b), mod_(mul_(d, a), m), add_(b, b));
		lemma_eq_ref(m);
	}
	let temp_111_0 = (mul_((mul_(b, d)), (add_(a, c))));
	let temp_111_1 = (add_((mul_((mul_(b, d)), a)), (mul_((mul_(b, d)), c))));
	assert(eq_(temp_111_0, temp_111_1)) by {
		lemma_mul_dist(mul_(b, d), a, c);
	}
	let temp_112_0 = (mul_((mul_(d, b)), (mod_((sub_(b, as_elem(26))), m))));
	let temp_112_1 = (mul_((mul_(d, b)), (mod_((sub_((mod_(b, m)), as_elem(26))), m))));
	assert(eq_(temp_112_0, temp_112_1)) by {
		cong_mul_(mul_(d, b), mod_(sub_(b, as_elem(26)), m), mul_(d, b), mod_(sub_(mod_(b, m), as_elem(26)), m));
		lemma_mod_sub_noop(b, as_elem(26), m);
		lemma_eq_ref(mul_(d, b));
	}
	let temp_113_0 = (mul_((mul_(d, c)), (mul_(a, as_elem(37)))));
	let temp_113_1 = (mul_(d, (mul_(c, (mul_(a, as_elem(37)))))));
	assert(eq_(temp_113_0, temp_113_1)) by {
		lemma_mul_assoc(d, c, mul_(a, as_elem(37)));
		lemma_eq_sym(temp_113_1, temp_113_0);
	}
	let temp_114_0 = (mul_((sub_(b, a)), (sub_(as_elem(75), c))));
	let temp_114_1 = (mul_((sub_(as_elem(75), c)), (sub_(b, a))));
	assert(eq_(temp_114_0, temp_114_1)) by {
		lemma_mul_comm(sub_(b, a), sub_(as_elem(75), c));
	}
	let temp_115_0 = (add_((add_(d, a)), (mul_(c, b))));
	let temp_115_1 = (add_((add_(d, a)), (mul_(b, c))));
	assert(eq_(temp_115_0, temp_115_1)) by {
		cong_add_(add_(d, a), mul_(c, b), add_(d, a), mul_(b, c));
		lemma_mul_comm(c, b);
		lemma_eq_ref(add_(d, a));
	}
	let temp_116_0 = (mul_((mul_(a, c)), (mul_(a, c))));
	let temp_116_1 = (mul_((mul_((mul_(a, c)), a)), c));
	assert(eq_(temp_116_0, temp_116_1)) by {
		lemma_mul_assoc(mul_(a, c), a, c);
	}
	let temp_117_0 = (mul_((mul_(d, b)), (mul_(a, b))));
	let temp_117_1 = (mul_((mul_((mul_(d, b)), a)), b));
	assert(eq_(temp_117_0, temp_117_1)) by {
		lemma_mul_assoc(mul_(d, b), a, b);
	}
	let temp_118_0 = (mul_((mul_(c, c)), (mul_(d, a))));
	let temp_118_1 = (mul_((mul_((mul_(c, c)), d)), a));
	assert(eq_(temp_118_0, temp_118_1)) by {
		lemma_mul_assoc(mul_(c, c), d, a);
	}
	let temp_119_0 = (mul_((mod_((sub_(c, a)), m)), (mul_(d, a))));
	let temp_119_1 = (mul_((mul_(d, a)), (mod_((sub_(c, a)), m))));
	assert(eq_(temp_119_0, temp_119_1)) by {
		lemma_mul_comm(mod_(sub_(c, a), m), mul_(d, a));
	}
	let temp_120_0 = (mul_(c, (add_(d, b))));
	let temp_120_1 = (mul_(c, (add_(b, d))));
	assert(eq_(temp_120_0, temp_120_1)) by {
		lemma_eq_ref(c);
		cong_mul_(c, add_(d, b), c, add_(b, d));
		lemma_add_comm(d, b);
	}
	let temp_121_0 = (mod_((mul_((mul_(b, d)), (mul_(c, a)))), m));
	let temp_121_1 = (mod_((mul_((mul_(c, a)), (mul_(b, d)))), m));
	assert(eq_(temp_121_0, temp_121_1)) by {
		lemma_mul_comm(mul_(b, d), mul_(c, a));
		cong_mod_(mul_(mul_(b, d), mul_(c, a)), m, mul_(mul_(c, a), mul_(b, d)), m);
		lemma_eq_ref(m);
	}
	let temp_122_0 = (mul_((sub_(a, c)), (mul_((mod_(as_elem(76), m)), d))));
	let temp_122_1 = (mul_((sub_(a, c)), (mul_((mod_((add_((mul_((mul_((add_(b, c)), (mul_(a, a)))), m)), as_elem(76))), m)), d))));
	assert(eq_(temp_122_0, temp_122_1)) by {
		lemma_mod_mul_vanish(as_elem(76), mul_(add_(b, c), mul_(a, a)), m);
		cong_mul_(sub_(a, c), mul_(mod_(as_elem(76), m), d), sub_(a, c), mul_(mod_(add_(mul_(mul_(add_(b, c), mul_(a, a)), m), as_elem(76)), m), d));
		lemma_eq_ref(d);
		lemma_eq_ref(sub_(a, c));
		cong_mul_(mod_(as_elem(76), m), d, mod_(add_(mul_(mul_(add_(b, c), mul_(a, a)), m), as_elem(76)), m), d);
	}

}

} // verus!