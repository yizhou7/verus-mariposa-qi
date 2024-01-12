use builtin_macros::*;
// use builtin::*;
mod nl_basics;
use crate::nl_basics::*;
verus! {

pub proof fn free_0(a: Elem, b: Elem, c: Elem, d: Elem, m: Elem)
{
	let temp_0_0 = (mul_((mod_((mul_(b, (mod_(c, m)))), m)), (mul_(b, c))));
	let temp_0_1 = (mul_((mod_((mul_(b, (mod_((add_((mul_((mul_((mul_(c, c)), (mul_(b, d)))), m)), c)), m)))), m)), (mul_(b, c))));
	assert(eq_(temp_0_0, temp_0_1)) by {
		lemma_eq_ref(b);
		cong_mul_(b, mod_(c, m), b, mod_(add_(mul_(mul_(mul_(c, c), mul_(b, d)), m), c), m));
		lemma_eq_ref(m);
		lemma_mod_mul_vanish(c, mul_(mul_(c, c), mul_(b, d)), m);
		cong_mul_(mod_(mul_(b, mod_(c, m)), m), mul_(b, c), mod_(mul_(b, mod_(add_(mul_(mul_(mul_(c, c), mul_(b, d)), m), c), m)), m), mul_(b, c));
		lemma_eq_ref(mul_(b, c));
		cong_mod_(mul_(b, mod_(c, m)), m, mul_(b, mod_(add_(mul_(mul_(mul_(c, c), mul_(b, d)), m), c), m)), m);
	}
	let temp_1_0 = (mul_((mul_(d, a)), (mod_((mul_(a, d)), m))));
	let temp_1_1 = (mul_(d, (mul_(a, (mod_((mul_(a, d)), m))))));
	assert(eq_(temp_1_0, temp_1_1)) by {
		lemma_eq_sym(temp_1_1, temp_1_0);
		lemma_mul_assoc(d, a, mod_(mul_(a, d), m));
	}
	let temp_2_0 = (mul_((mul_((mod_(b, m)), c)), (mul_(a, d))));
	let temp_2_1 = (mul_((mul_(c, (mod_(b, m)))), (mul_(a, d))));
	assert(eq_(temp_2_0, temp_2_1)) by {
		lemma_mul_comm(mod_(b, m), c);
		cong_mul_(mul_(mod_(b, m), c), mul_(a, d), mul_(c, mod_(b, m)), mul_(a, d));
		lemma_eq_ref(mul_(a, d));
	}
	let temp_3_0 = (add_((mul_(a, c)), (mul_(d, c))));
	let temp_3_1 = (add_((mul_(a, c)), (mul_(c, d))));
	assert(eq_(temp_3_0, temp_3_1)) by {
		cong_add_(mul_(a, c), mul_(d, c), mul_(a, c), mul_(c, d));
		lemma_mul_comm(d, c);
		lemma_eq_ref(mul_(a, c));
	}
	let temp_4_0 = (mul_((mod_((mul_(b, (mod_(b, m)))), m)), (mul_(b, b))));
	let temp_4_1 = (mul_((mul_(b, b)), (mod_((mul_(b, (mod_(b, m)))), m))));
	assert(eq_(temp_4_0, temp_4_1)) by {
		lemma_mul_comm(mod_(mul_(b, mod_(b, m)), m), mul_(b, b));
	}
	let temp_5_0 = (mul_((mul_(c, b)), (mul_(b, b))));
	let temp_5_1 = (mul_((mul_(b, c)), (mul_(b, b))));
	assert(eq_(temp_5_0, temp_5_1)) by {
		cong_mul_(mul_(c, b), mul_(b, b), mul_(b, c), mul_(b, b));
		lemma_mul_comm(c, b);
		lemma_mul_comm(b, b);
	}
	let temp_6_0 = (mul_((mul_(a, d)), (mul_(a, d))));
	let temp_6_1 = (mul_(a, (mul_(d, (mul_(a, d))))));
	assert(eq_(temp_6_0, temp_6_1)) by {
		lemma_eq_sym(temp_6_1, temp_6_0);
		lemma_mul_assoc(a, d, mul_(a, d));
	}
	let temp_7_0 = (mod_((add_((sub_((mod_(b, m)), b)), (mul_(d, b)))), m));
	let temp_7_1 = (mod_((add_((sub_((mod_((add_((mul_((mod_((mul_((mul_(d, a)), (mul_(a, b)))), m)), m)), b)), m)), b)), (mul_(d, b)))), m));
	assert(eq_(temp_7_0, temp_7_1)) by {
		lemma_mod_mul_vanish(b, mod_(mul_(mul_(d, a), mul_(a, b)), m), m);
		cong_mod_(add_(sub_(mod_(b, m), b), mul_(d, b)), m, add_(sub_(mod_(add_(mul_(mod_(mul_(mul_(d, a), mul_(a, b)), m), m), b), m), b), mul_(d, b)), m);
		lemma_eq_ref(mul_(d, b));
		cong_sub_(mod_(b, m), b, mod_(add_(mul_(mod_(mul_(mul_(d, a), mul_(a, b)), m), m), b), m), b);
		cong_add_(sub_(mod_(b, m), b), mul_(d, b), sub_(mod_(add_(mul_(mod_(mul_(mul_(d, a), mul_(a, b)), m), m), b), m), b), mul_(d, b));
		lemma_eq_ref(m);
		lemma_eq_ref(b);
	}
	let temp_8_0 = (add_((mul_(a, as_elem(70))), (mul_(b, d))));
	let temp_8_1 = (add_((mul_(b, d)), (mul_(a, as_elem(70)))));
	assert(eq_(temp_8_0, temp_8_1)) by {
		lemma_add_comm(mul_(a, as_elem(70)), mul_(b, d));
	}
	let temp_9_0 = (mul_((mul_(b, a)), (sub_(a, as_elem(11)))));
	let temp_9_1 = (mul_(b, (mul_(a, (sub_(a, as_elem(11)))))));
	assert(eq_(temp_9_0, temp_9_1)) by {
		lemma_eq_sym(temp_9_1, temp_9_0);
		lemma_mul_assoc(b, a, sub_(a, as_elem(11)));
	}
	let temp_10_0 = (mul_((mul_(c, c)), (sub_(as_elem(95), d))));
	let temp_10_1 = (mul_((mul_(c, c)), (sub_(as_elem(95), d))));
	assert(eq_(temp_10_0, temp_10_1)) by {
		lemma_eq_ref(temp_10_0);
	}
	let temp_11_0 = (mul_((mul_(a, b)), (mul_((mod_(a, m)), b))));
	let temp_11_1 = (mul_(a, (mul_(b, (mul_((mod_(a, m)), b))))));
	assert(eq_(temp_11_0, temp_11_1)) by {
		lemma_eq_sym(temp_11_1, temp_11_0);
		lemma_mul_assoc(a, b, mul_(mod_(a, m), b));
	}
	let temp_12_0 = (mul_((mul_(a, b)), (mul_(a, b))));
	let temp_12_1 = (mul_(a, (mul_(b, (mul_(a, b))))));
	assert(eq_(temp_12_0, temp_12_1)) by {
		lemma_eq_sym(temp_12_1, temp_12_0);
		lemma_mul_assoc(a, b, mul_(a, b));
	}
	let temp_13_0 = (add_((mul_(c, (mod_(c, m)))), (sub_(a, a))));
	let temp_13_1 = (add_((mul_(c, (mod_((add_(c, (mul_((mul_((mul_(b, a)), (add_(c, b)))), m)))), m)))), (sub_(a, a))));
	assert(eq_(temp_13_0, temp_13_1)) by {
		cong_mul_(c, mod_(c, m), c, mod_(add_(c, mul_(mul_(mul_(b, a), add_(c, b)), m)), m));
		lemma_eq_ref(sub_(a, a));
		lemma_eq_ref(c);
		lemma_mod_mul_vanish(c, mul_(mul_(b, a), add_(c, b)), m);
		cong_add_(mul_(c, mod_(c, m)), sub_(a, a), mul_(c, mod_(add_(c, mul_(mul_(mul_(b, a), add_(c, b)), m)), m)), sub_(a, a));
	}
	let temp_14_0 = (mul_((mod_((mul_(a, b)), m)), (mul_(b, d))));
	let temp_14_1 = (mul_((mod_((add_((mul_((mul_((mul_(as_elem(37), a)), (add_(a, (mod_(c, m)))))), m)), (mul_(a, b)))), m)), (mul_(b, d))));
	assert(eq_(temp_14_0, temp_14_1)) by {
		lemma_mod_mul_vanish(mul_(a, b), mul_(mul_(as_elem(37), a), add_(a, mod_(c, m))), m);
		cong_mul_(mod_(mul_(a, b), m), mul_(b, d), mod_(add_(mul_(mul_(mul_(as_elem(37), a), add_(a, mod_(c, m))), m), mul_(a, b)), m), mul_(b, d));
		lemma_eq_ref(mul_(b, d));
	}
	let temp_15_0 = (mul_((mul_(c, a)), (mul_(b, d))));
	let temp_15_1 = (mul_((mul_(c, a)), (mul_(d, b))));
	assert(eq_(temp_15_0, temp_15_1)) by {
		cong_mul_(mul_(c, a), mul_(b, d), mul_(c, a), mul_(d, b));
		lemma_mul_comm(b, d);
		lemma_eq_ref(mul_(c, a));
	}
	let temp_16_0 = (add_((mul_(d, a)), (mul_(b, a))));
	let temp_16_1 = (add_((mul_(d, a)), (mul_(a, b))));
	assert(eq_(temp_16_0, temp_16_1)) by {
		cong_add_(mul_(d, a), mul_(b, a), mul_(d, a), mul_(a, b));
		lemma_mul_comm(b, a);
		lemma_eq_ref(mul_(d, a));
	}
	let temp_17_0 = (mul_((mul_(a, c)), (mul_(a, b))));
	let temp_17_1 = (mul_((mul_((mul_(a, c)), a)), b));
	assert(eq_(temp_17_0, temp_17_1)) by {
		lemma_mul_assoc(mul_(a, c), a, b);
	}
	let temp_18_0 = (sub_((mul_(d, a)), (mul_(a, c))));
	let temp_18_1 = (sub_((mul_(d, a)), (mul_(c, a))));
	assert(eq_(temp_18_0, temp_18_1)) by {
		cong_sub_(mul_(d, a), mul_(a, c), mul_(d, a), mul_(c, a));
		lemma_mul_comm(a, c);
		lemma_eq_ref(mul_(d, a));
	}
	let temp_19_0 = (mul_((mul_(c, as_elem(16))), (mul_(c, b))));
	let temp_19_1 = (mul_((mul_(as_elem(16), c)), (mul_(c, b))));
	assert(eq_(temp_19_0, temp_19_1)) by {
		cong_mul_(mul_(c, as_elem(16)), mul_(c, b), mul_(as_elem(16), c), mul_(c, b));
		lemma_mul_comm(c, as_elem(16));
		lemma_eq_ref(mul_(c, b));
	}
	let temp_20_0 = (mul_((sub_(d, a)), (mul_(c, b))));
	let temp_20_1 = (mul_((mul_((sub_(d, a)), c)), b));
	assert(eq_(temp_20_0, temp_20_1)) by {
		lemma_mul_assoc(sub_(d, a), c, b);
	}
	let temp_21_0 = (mul_((sub_(b, b)), (mul_(b, b))));
	let temp_21_1 = (mul_((mul_((sub_(b, b)), b)), b));
	assert(eq_(temp_21_0, temp_21_1)) by {
		lemma_mul_assoc(sub_(b, b), b, b);
	}
	let temp_22_0 = (mul_((mul_(b, b)), (mul_(b, c))));
	let temp_22_1 = (mul_((mul_((mul_(b, b)), b)), c));
	assert(eq_(temp_22_0, temp_22_1)) by {
		lemma_mul_assoc(mul_(b, b), b, c);
	}
	let temp_23_0 = (mul_((mul_(b, a)), (mul_(c, b))));
	let temp_23_1 = (mul_((mul_(c, b)), (mul_(b, a))));
	assert(eq_(temp_23_0, temp_23_1)) by {
		lemma_mul_comm(mul_(b, a), mul_(c, b));
	}
	let temp_24_0 = (mul_((mul_(c, a)), (mul_(d, a))));
	let temp_24_1 = (mul_((mul_(d, a)), (mul_(c, a))));
	assert(eq_(temp_24_0, temp_24_1)) by {
		lemma_mul_comm(mul_(c, a), mul_(d, a));
	}
	let temp_25_0 = (mul_((mul_((mod_(a, m)), (mod_(c, m)))), (mod_((mul_(b, a)), m))));
	let temp_25_1 = (mul_((mul_((mod_(a, m)), (mod_(c, m)))), (mod_((add_((mul_(b, a)), (mul_((mul_((mul_(d, b)), (mul_(a, c)))), m)))), m))));
	assert(eq_(temp_25_0, temp_25_1)) by {
		lemma_mod_mul_vanish(mul_(b, a), mul_(mul_(d, b), mul_(a, c)), m);
		cong_mul_(mul_(mod_(a, m), mod_(c, m)), mod_(mul_(b, a), m), mul_(mod_(a, m), mod_(c, m)), mod_(add_(mul_(b, a), mul_(mul_(mul_(d, b), mul_(a, c)), m)), m));
		lemma_eq_ref(mul_(mod_(a, m), mod_(c, m)));
	}
	let temp_26_0 = (mul_((sub_(b, a)), (mul_(d, d))));
	let temp_26_1 = (sub_((mul_(b, (mul_(d, d)))), (mul_(a, (mul_(d, d))))));
	assert(eq_(temp_26_0, temp_26_1)) by {
		lemma_mul_dist(mul_(d, d), b, a);
	}
	let temp_27_0 = (mod_((add_((mul_(d, b)), (mul_(a, a)))), m));
	let temp_27_1 = (mod_((add_((mul_(a, a)), (mul_(d, b)))), m));
	assert(eq_(temp_27_0, temp_27_1)) by {
		lemma_add_comm(mul_(d, b), mul_(a, a));
		cong_mod_(add_(mul_(d, b), mul_(a, a)), m, add_(mul_(a, a), mul_(d, b)), m);
		lemma_eq_ref(m);
	}
	let temp_28_0 = (mul_((mul_(d, b)), (mul_(b, a))));
	let temp_28_1 = (mul_(d, (mul_(b, (mul_(b, a))))));
	assert(eq_(temp_28_0, temp_28_1)) by {
		lemma_eq_sym(temp_28_1, temp_28_0);
		lemma_mul_assoc(d, b, mul_(b, a));
	}
	let temp_29_0 = (mul_((mul_(b, a)), (mul_(c, b))));
	let temp_29_1 = (mul_((mul_((mul_(b, a)), c)), b));
	assert(eq_(temp_29_0, temp_29_1)) by {
		lemma_mul_assoc(mul_(b, a), c, b);
	}
	let temp_30_0 = (mod_((mul_((mod_((mul_(a, (mod_(b, m)))), m)), (add_(d, b)))), m));
	let temp_30_1 = (mod_((mul_((mod_((sub_((mul_(a, (mod_(b, m)))), (mul_((mul_((sub_((mod_(c, m)), d)), (mul_(b, b)))), m)))), m)), (add_(d, b)))), m));
	assert(eq_(temp_30_0, temp_30_1)) by {
		lemma_mod_mul_vanish(mul_(a, mod_(b, m)), mul_(sub_(mod_(c, m), d), mul_(b, b)), m);
		cong_mod_(mul_(mod_(mul_(a, mod_(b, m)), m), add_(d, b)), m, mul_(mod_(sub_(mul_(a, mod_(b, m)), mul_(mul_(sub_(mod_(c, m), d), mul_(b, b)), m)), m), add_(d, b)), m);
		lemma_eq_ref(m);
		lemma_eq_ref(add_(d, b));
		cong_mul_(mod_(mul_(a, mod_(b, m)), m), add_(d, b), mod_(sub_(mul_(a, mod_(b, m)), mul_(mul_(sub_(mod_(c, m), d), mul_(b, b)), m)), m), add_(d, b));
	}
	let temp_31_0 = (mul_((mul_(a, c)), (mul_(a, a))));
	let temp_31_1 = (mul_((mul_(a, a)), (mul_(a, c))));
	assert(eq_(temp_31_0, temp_31_1)) by {
		lemma_mul_comm(mul_(a, c), mul_(a, a));
	}
	let temp_32_0 = (mul_((mul_(as_elem(40), d)), (mod_((mul_(d, c)), m))));
	let temp_32_1 = (mul_((mul_(d, as_elem(40))), (mod_((mul_(d, c)), m))));
	assert(eq_(temp_32_0, temp_32_1)) by {
		lemma_mul_comm(as_elem(40), d);
		cong_mul_(mul_(as_elem(40), d), mod_(mul_(d, c), m), mul_(d, as_elem(40)), mod_(mul_(d, c), m));
		lemma_eq_ref(mod_(mul_(d, c), m));
	}
	let temp_33_0 = (add_((mul_(b, b)), (mul_((mod_(c, m)), c))));
	let temp_33_1 = (add_((mul_((mod_(c, m)), c)), (mul_(b, b))));
	assert(eq_(temp_33_0, temp_33_1)) by {
		lemma_add_comm(mul_(b, b), mul_(mod_(c, m), c));
	}
	let temp_34_0 = (mul_((mul_(b, a)), (sub_(c, a))));
	let temp_34_1 = (mul_((mul_(a, b)), (sub_(c, a))));
	assert(eq_(temp_34_0, temp_34_1)) by {
		cong_mul_(mul_(b, a), sub_(c, a), mul_(a, b), sub_(c, a));
		lemma_mul_comm(b, a);
		lemma_eq_ref(sub_(c, a));
	}
	let temp_35_0 = (mul_((mul_(c, (mod_(a, m)))), (mul_(b, a))));
	let temp_35_1 = (mul_((mul_((mul_(c, (mod_(a, m)))), b)), a));
	assert(eq_(temp_35_0, temp_35_1)) by {
		lemma_mul_assoc(mul_(c, mod_(a, m)), b, a);
	}
	let temp_36_0 = (mul_((mul_(c, (mod_(as_elem(33), m)))), (mul_(b, c))));
	let temp_36_1 = (mul_((mul_((mul_(c, (mod_(as_elem(33), m)))), b)), c));
	assert(eq_(temp_36_0, temp_36_1)) by {
		lemma_mul_assoc(mul_(c, mod_(as_elem(33), m)), b, c);
	}
	let temp_37_0 = (mul_((mul_(d, b)), (mul_(d, d))));
	let temp_37_1 = (mul_((mul_(d, b)), (mul_(d, d))));
	assert(eq_(temp_37_0, temp_37_1)) by {
		lemma_eq_ref(temp_37_0);
	}
	let temp_38_0 = (mul_((mul_(a, a)), (mul_(as_elem(12), d))));
	let temp_38_1 = (mul_((mul_(as_elem(12), d)), (mul_(a, a))));
	assert(eq_(temp_38_0, temp_38_1)) by {
		lemma_mul_comm(mul_(a, a), mul_(as_elem(12), d));
	}
	let temp_39_0 = (mod_((mul_((add_((mod_(c, m)), (mod_(b, m)))), (mul_(c, c)))), m));
	let temp_39_1 = (mod_((mul_((add_((mod_(c, m)), (mod_((add_(b, (mul_((mul_(b, (sub_(c, c)))), m)))), m)))), (mul_(c, c)))), m));
	assert(eq_(temp_39_0, temp_39_1)) by {
		lemma_mul_comm(c, c);
		lemma_mod_mul_vanish(b, mul_(b, sub_(c, c)), m);
		cong_mod_(mul_(add_(mod_(c, m), mod_(b, m)), mul_(c, c)), m, mul_(add_(mod_(c, m), mod_(add_(b, mul_(mul_(b, sub_(c, c)), m)), m)), mul_(c, c)), m);
		lemma_eq_ref(m);
		cong_mul_(add_(mod_(c, m), mod_(b, m)), mul_(c, c), add_(mod_(c, m), mod_(add_(b, mul_(mul_(b, sub_(c, c)), m)), m)), mul_(c, c));
		lemma_eq_ref(mod_(c, m));
		cong_add_(mod_(c, m), mod_(b, m), mod_(c, m), mod_(add_(b, mul_(mul_(b, sub_(c, c)), m)), m));
	}
	let temp_40_0 = (mul_((mul_(a, a)), (mul_(c, (mod_(as_elem(21), m))))));
	let temp_40_1 = (mul_((mul_(a, a)), (mul_(c, (mod_((sub_(as_elem(21), (mul_((mul_((mul_(a, b)), (mul_(a, d)))), m)))), m))))));
	assert(eq_(temp_40_0, temp_40_1)) by {
		lemma_mul_comm(a, a);
		cong_mul_(mul_(a, a), mul_(c, mod_(as_elem(21), m)), mul_(a, a), mul_(c, mod_(sub_(as_elem(21), mul_(mul_(mul_(a, b), mul_(a, d)), m)), m)));
		lemma_mod_mul_vanish(as_elem(21), mul_(mul_(a, b), mul_(a, d)), m);
		lemma_eq_ref(c);
		cong_mul_(c, mod_(as_elem(21), m), c, mod_(sub_(as_elem(21), mul_(mul_(mul_(a, b), mul_(a, d)), m)), m));
	}
	let temp_41_0 = (mul_((mul_(a, d)), (mul_(d, c))));
	let temp_41_1 = (mul_((mul_(a, d)), (mul_(c, d))));
	assert(eq_(temp_41_0, temp_41_1)) by {
		cong_mul_(mul_(a, d), mul_(d, c), mul_(a, d), mul_(c, d));
		lemma_mul_comm(d, c);
		lemma_eq_ref(mul_(a, d));
	}
	let temp_42_0 = (mul_((mul_(d, c)), (add_(a, a))));
	let temp_42_1 = (mul_((mul_(d, c)), (add_(a, a))));
	assert(eq_(temp_42_0, temp_42_1)) by {
		lemma_eq_ref(temp_42_0);
	}
	let temp_43_0 = (mod_((mul_((mul_(c, a)), (mul_(c, b)))), m));
	let temp_43_1 = (mod_((mul_(c, (mul_(a, (mul_(c, b)))))), m));
	assert(eq_(temp_43_0, temp_43_1)) by {
		lemma_mul_assoc(c, a, mul_(c, b));
		cong_mod_(mul_(mul_(c, a), mul_(c, b)), m, mul_(c, mul_(a, mul_(c, b))), m);
		lemma_eq_sym(mul_(c, mul_(a, mul_(c, b))), mul_(mul_(c, a), mul_(c, b)));
		lemma_eq_ref(m);
	}
	let temp_44_0 = (sub_((mul_(a, d)), a));
	let temp_44_1 = (sub_((mul_(d, a)), a));
	assert(eq_(temp_44_0, temp_44_1)) by {
		cong_sub_(mul_(a, d), a, mul_(d, a), a);
		lemma_mul_comm(a, d);
		lemma_eq_ref(a);
	}
	let temp_45_0 = (sub_((mul_(b, a)), (mul_(b, (mod_(as_elem(3), m))))));
	let temp_45_1 = (sub_((mul_(a, b)), (mul_(b, (mod_(as_elem(3), m))))));
	assert(eq_(temp_45_0, temp_45_1)) by {
		lemma_mul_comm(b, a);
		cong_sub_(mul_(b, a), mul_(b, mod_(as_elem(3), m)), mul_(a, b), mul_(b, mod_(as_elem(3), m)));
		lemma_eq_ref(mul_(b, mod_(as_elem(3), m)));
	}
	let temp_46_0 = (mul_((mul_(a, c)), (add_(b, c))));
	let temp_46_1 = (mul_((mul_(a, c)), (add_(c, b))));
	assert(eq_(temp_46_0, temp_46_1)) by {
		cong_mul_(mul_(a, c), add_(b, c), mul_(a, c), add_(c, b));
		lemma_add_comm(b, c);
		lemma_eq_ref(mul_(a, c));
	}
	let temp_47_0 = (mul_((mod_((mul_(d, a)), m)), (mul_(b, c))));
	let temp_47_1 = (mul_((mul_((mod_((mul_(d, a)), m)), b)), c));
	assert(eq_(temp_47_0, temp_47_1)) by {
		lemma_mul_assoc(mod_(mul_(d, a), m), b, c);
	}
	let temp_48_0 = (mul_((add_(c, d)), (mul_(a, c))));
	let temp_48_1 = (mul_((mul_((add_(c, d)), a)), c));
	assert(eq_(temp_48_0, temp_48_1)) by {
		lemma_mul_assoc(add_(c, d), a, c);
	}
	let temp_49_0 = (add_((mul_(as_elem(98), b)), (sub_((mod_(b, m)), (mod_(a, m))))));
	let temp_49_1 = (add_((sub_((mod_(b, m)), (mod_(a, m)))), (mul_(as_elem(98), b))));
	assert(eq_(temp_49_0, temp_49_1)) by {
		lemma_add_comm(mul_(as_elem(98), b), sub_(mod_(b, m), mod_(a, m)));
	}
	let temp_50_0 = (mul_((mul_(b, c)), (mul_(b, c))));
	let temp_50_1 = (mul_((mul_(b, c)), (mul_(c, b))));
	assert(eq_(temp_50_0, temp_50_1)) by {
		cong_mul_(mul_(b, c), mul_(b, c), mul_(b, c), mul_(c, b));
		lemma_mul_comm(b, c);
		lemma_eq_ref(mul_(b, c));
	}
	let temp_51_0 = (mul_((mod_((mul_(a, a)), m)), (mul_(b, c))));
	let temp_51_1 = (mul_((mod_((add_((mul_((mul_((mul_(d, b)), (mul_(b, d)))), m)), (mul_(a, a)))), m)), (mul_(b, c))));
	assert(eq_(temp_51_0, temp_51_1)) by {
		lemma_mod_mul_vanish(mul_(a, a), mul_(mul_(d, b), mul_(b, d)), m);
		cong_mul_(mod_(mul_(a, a), m), mul_(b, c), mod_(add_(mul_(mul_(mul_(d, b), mul_(b, d)), m), mul_(a, a)), m), mul_(b, c));
		lemma_eq_ref(mul_(b, c));
	}
	let temp_52_0 = (mul_((mul_((mod_(a, m)), a)), (sub_(a, as_elem(48)))));
	let temp_52_1 = (mul_((mul_((mod_((add_((mul_((mul_((mul_(c, c)), (mul_(a, b)))), m)), a)), m)), a)), (sub_(a, as_elem(48)))));
	assert(eq_(temp_52_0, temp_52_1)) by {
		lemma_mod_mul_vanish(a, mul_(mul_(c, c), mul_(a, b)), m);
		cong_mul_(mul_(mod_(a, m), a), sub_(a, as_elem(48)), mul_(mod_(add_(mul_(mul_(mul_(c, c), mul_(a, b)), m), a), m), a), sub_(a, as_elem(48)));
		lemma_eq_ref(a);
		cong_mul_(mod_(a, m), a, mod_(add_(mul_(mul_(mul_(c, c), mul_(a, b)), m), a), m), a);
		lemma_eq_ref(sub_(a, as_elem(48)));
	}
	let temp_53_0 = (mod_((mul_((add_(b, d)), (mul_(b, c)))), m));
	let temp_53_1 = (mod_((mul_((add_(b, d)), (mul_(c, b)))), m));
	assert(eq_(temp_53_0, temp_53_1)) by {
		lemma_mul_comm(b, c);
		cong_mod_(mul_(add_(b, d), mul_(b, c)), m, mul_(add_(b, d), mul_(c, b)), m);
		lemma_eq_ref(add_(b, d));
		cong_mul_(add_(b, d), mul_(b, c), add_(b, d), mul_(c, b));
		lemma_eq_ref(m);
	}
	let temp_54_0 = (mul_((mul_(b, b)), (mul_(a, c))));
	let temp_54_1 = (mul_(b, (mul_(b, (mul_(a, c))))));
	assert(eq_(temp_54_0, temp_54_1)) by {
		lemma_eq_sym(temp_54_1, temp_54_0);
		lemma_mul_assoc(b, b, mul_(a, c));
	}
	let temp_55_0 = (mul_((mul_((mod_(b, m)), b)), (mul_(a, (mod_(b, m))))));
	let temp_55_1 = (mul_((mod_(b, m)), (mul_(b, (mul_(a, (mod_(b, m))))))));
	assert(eq_(temp_55_0, temp_55_1)) by {
		lemma_eq_sym(temp_55_1, temp_55_0);
		lemma_mul_assoc(mod_(b, m), b, mul_(a, mod_(b, m)));
	}
	let temp_56_0 = (add_((mul_(a, b)), (mul_(d, c))));
	let temp_56_1 = (add_((mul_(d, c)), (mul_(a, b))));
	assert(eq_(temp_56_0, temp_56_1)) by {
		lemma_add_comm(mul_(a, b), mul_(d, c));
	}
	let temp_57_0 = (mul_((mul_(b, c)), (mul_(d, b))));
	let temp_57_1 = (mul_((mul_(b, c)), (mul_(b, d))));
	assert(eq_(temp_57_0, temp_57_1)) by {
		cong_mul_(mul_(b, c), mul_(d, b), mul_(b, c), mul_(b, d));
		lemma_mul_comm(d, b);
		lemma_eq_ref(mul_(b, c));
	}
	let temp_58_0 = (mul_((add_(b, a)), (mul_(b, b))));
	let temp_58_1 = (mul_((mul_((add_(b, a)), b)), b));
	assert(eq_(temp_58_0, temp_58_1)) by {
		lemma_mul_assoc(add_(b, a), b, b);
	}
	let temp_59_0 = (add_((mul_(a, c)), (mul_(c, c))));
	let temp_59_1 = (add_((mul_(a, c)), (mul_(c, c))));
	assert(eq_(temp_59_0, temp_59_1)) by {
		lemma_eq_ref(temp_59_0);
	}
	let temp_60_0 = (mod_((mul_((mul_(d, a)), (mul_(b, a)))), m));
	let temp_60_1 = (mod_((mul_((mul_(b, a)), (mul_(d, a)))), m));
	assert(eq_(temp_60_0, temp_60_1)) by {
		lemma_mul_comm(mul_(d, a), mul_(b, a));
		cong_mod_(mul_(mul_(d, a), mul_(b, a)), m, mul_(mul_(b, a), mul_(d, a)), m);
		lemma_eq_ref(m);
	}
	let temp_61_0 = (mul_((mul_(c, c)), (mul_(d, b))));
	let temp_61_1 = (mul_((mul_(c, c)), (mul_(b, d))));
	assert(eq_(temp_61_0, temp_61_1)) by {
		cong_mul_(mul_(c, c), mul_(d, b), mul_(c, c), mul_(b, d));
		lemma_mul_comm(c, c);
		lemma_mul_comm(d, b);
	}
	let temp_62_0 = (mul_((mod_((sub_(b, d)), m)), (mul_(b, d))));
	let temp_62_1 = (mul_((mod_((sub_(b, d)), m)), (mul_(d, b))));
	assert(eq_(temp_62_0, temp_62_1)) by {
		cong_mul_(mod_(sub_(b, d), m), mul_(b, d), mod_(sub_(b, d), m), mul_(d, b));
		lemma_mul_comm(b, d);
		lemma_eq_ref(mod_(sub_(b, d), m));
	}
	let temp_63_0 = (mul_((mul_(b, (mod_(a, m)))), (sub_(a, d))));
	let temp_63_1 = (mul_((sub_(a, d)), (mul_(b, (mod_(a, m))))));
	assert(eq_(temp_63_0, temp_63_1)) by {
		lemma_mul_comm(mul_(b, mod_(a, m)), sub_(a, d));
	}
	let temp_64_0 = (mul_((mul_(c, b)), (mul_(c, c))));
	let temp_64_1 = (mul_((mul_(c, c)), (mul_(c, b))));
	assert(eq_(temp_64_0, temp_64_1)) by {
		lemma_mul_comm(mul_(c, b), mul_(c, c));
	}
	let temp_65_0 = (mul_((mul_(a, d)), (mul_(c, (mod_(a, m))))));
	let temp_65_1 = (mul_(a, (mul_(d, (mul_(c, (mod_(a, m))))))));
	assert(eq_(temp_65_0, temp_65_1)) by {
		lemma_mul_assoc(a, d, mul_(c, mod_(a, m)));
		lemma_eq_sym(temp_65_1, temp_65_0);
	}
	let temp_66_0 = (mul_((mul_(c, a)), (mod_((sub_(d, (mod_(a, m)))), m))));
	let temp_66_1 = (mul_((mul_(a, c)), (mod_((sub_(d, (mod_(a, m)))), m))));
	assert(eq_(temp_66_0, temp_66_1)) by {
		lemma_mul_comm(c, a);
		cong_mul_(mul_(c, a), mod_(sub_(d, mod_(a, m)), m), mul_(a, c), mod_(sub_(d, mod_(a, m)), m));
		lemma_eq_ref(mod_(sub_(d, mod_(a, m)), m));
	}
	let temp_67_0 = (mul_((mul_((mod_(d, m)), d)), (mul_(c, b))));
	let temp_67_1 = (mul_((mul_((mod_(d, m)), d)), (mul_(b, c))));
	assert(eq_(temp_67_0, temp_67_1)) by {
		lemma_mul_comm(c, b);
		cong_mul_(mul_(mod_(d, m), d), mul_(c, b), mul_(mod_(d, m), d), mul_(b, c));
		lemma_eq_ref(mul_(mod_(d, m), d));
	}
	let temp_68_0 = (sub_((mul_(a, a)), (mul_(b, c))));
	let temp_68_1 = (sub_((mul_(a, a)), (mul_(c, b))));
	assert(eq_(temp_68_0, temp_68_1)) by {
		cong_sub_(mul_(a, a), mul_(b, c), mul_(a, a), mul_(c, b));
		lemma_mul_comm(b, c);
		lemma_eq_ref(mul_(a, a));
	}
	let temp_69_0 = (mod_((mul_((sub_(a, as_elem(67))), (mul_(a, b)))), m));
	let temp_69_1 = (mod_((sub_((mul_((sub_(a, as_elem(67))), (mul_(a, b)))), (mul_((mul_((mul_(d, d)), (mul_(c, d)))), m)))), m));
	assert(eq_(temp_69_0, temp_69_1)) by {
		lemma_mod_mul_vanish(mul_(sub_(a, as_elem(67)), mul_(a, b)), mul_(mul_(d, d), mul_(c, d)), m);
	}
	let temp_70_0 = (mul_((mod_((sub_(d, c)), m)), (mod_((mul_(d, d)), m))));
	let temp_70_1 = (mul_((mod_((sub_((mod_(d, m)), c)), m)), (mod_((mul_(d, d)), m))));
	assert(eq_(temp_70_0, temp_70_1)) by {
		cong_mul_(mod_(sub_(d, c), m), mod_(mul_(d, d), m), mod_(sub_(mod_(d, m), c), m), mod_(mul_(d, d), m));
		lemma_mod_sub_noop(d, c, m);
		lemma_eq_ref(mod_(mul_(d, d), m));
	}
	let temp_71_0 = (mod_((mul_((mul_(b, c)), (mul_(c, c)))), m));
	let temp_71_1 = (mod_((mul_((mul_(c, c)), (mul_(b, c)))), m));
	assert(eq_(temp_71_0, temp_71_1)) by {
		cong_mod_(mul_(mul_(b, c), mul_(c, c)), m, mul_(mul_(c, c), mul_(b, c)), m);
		lemma_mul_comm(mul_(b, c), mul_(c, c));
		lemma_eq_ref(m);
	}
	let temp_72_0 = (mul_((mul_(c, d)), (mul_(c, c))));
	let temp_72_1 = (mul_(c, (mul_(d, (mul_(c, c))))));
	assert(eq_(temp_72_0, temp_72_1)) by {
		lemma_eq_sym(temp_72_1, temp_72_0);
		lemma_mul_assoc(c, d, mul_(c, c));
	}
	let temp_73_0 = (mul_((mul_(c, c)), (sub_(c, (mod_(a, m))))));
	let temp_73_1 = (mul_((mul_(c, c)), (sub_(c, (mod_(a, m))))));
	assert(eq_(temp_73_0, temp_73_1)) by {
		lemma_eq_ref(temp_73_0);
	}
	let temp_74_0 = (sub_((mul_(a, c)), (mul_(c, a))));
	let temp_74_1 = (sub_((mul_(c, a)), (mul_(c, a))));
	assert(eq_(temp_74_0, temp_74_1)) by {
		cong_sub_(mul_(a, c), mul_(c, a), mul_(c, a), mul_(c, a));
		lemma_mul_comm(a, c);
		lemma_eq_ref(mul_(c, a));
	}
	let temp_75_0 = (mul_((mul_(d, c)), (mod_((mul_(c, c)), m))));
	let temp_75_1 = (mul_(d, (mul_(c, (mod_((mul_(c, c)), m))))));
	assert(eq_(temp_75_0, temp_75_1)) by {
		lemma_eq_sym(temp_75_1, temp_75_0);
		lemma_mul_assoc(d, c, mod_(mul_(c, c), m));
	}
	let temp_76_0 = (mul_((mod_(a, m)), (mul_(c, b))));
	let temp_76_1 = (mul_((mod_((add_(a, (mul_((add_((mul_(d, b)), (mod_((mul_(a, c)), m)))), m)))), m)), (mul_(c, b))));
	assert(eq_(temp_76_0, temp_76_1)) by {
		lemma_mod_mul_vanish(a, add_(mul_(d, b), mod_(mul_(a, c), m)), m);
		cong_mul_(mod_(a, m), mul_(c, b), mod_(add_(a, mul_(add_(mul_(d, b), mod_(mul_(a, c), m)), m)), m), mul_(c, b));
		lemma_eq_ref(mul_(c, b));
	}
	let temp_77_0 = (mul_((mod_((mul_(a, b)), m)), (mul_(d, a))));
	let temp_77_1 = (mul_((mod_((mul_(b, a)), m)), (mul_(d, a))));
	assert(eq_(temp_77_0, temp_77_1)) by {
		lemma_mul_comm(a, b);
		cong_mul_(mod_(mul_(a, b), m), mul_(d, a), mod_(mul_(b, a), m), mul_(d, a));
		cong_mod_(mul_(a, b), m, mul_(b, a), m);
		lemma_eq_ref(mul_(d, a));
		lemma_eq_ref(m);
	}
	let temp_78_0 = (mul_((mod_((mul_(b, (mod_(d, m)))), m)), (mul_((mod_(a, m)), b))));
	let temp_78_1 = (mul_((mod_((add_((mul_(b, (mod_(d, m)))), (mul_((mul_((mul_(c, b)), (sub_((mod_(a, m)), d)))), m)))), m)), (mul_((mod_(a, m)), b))));
	assert(eq_(temp_78_0, temp_78_1)) by {
		lemma_mod_mul_vanish(mul_(b, mod_(d, m)), mul_(mul_(c, b), sub_(mod_(a, m), d)), m);
		cong_mul_(mod_(mul_(b, mod_(d, m)), m), mul_(mod_(a, m), b), mod_(add_(mul_(b, mod_(d, m)), mul_(mul_(mul_(c, b), sub_(mod_(a, m), d)), m)), m), mul_(mod_(a, m), b));
		lemma_eq_ref(mul_(mod_(a, m), b));
	}
	let temp_79_0 = (mul_((mul_((mod_(b, m)), c)), (sub_(c, a))));
	let temp_79_1 = (mul_((mod_(b, m)), (mul_(c, (sub_(c, a))))));
	assert(eq_(temp_79_0, temp_79_1)) by {
		lemma_mul_assoc(mod_(b, m), c, sub_(c, a));
		lemma_eq_sym(temp_79_1, temp_79_0);
	}
	let temp_80_0 = (mul_((mul_(d, c)), (mul_(a, c))));
	let temp_80_1 = (mul_((mul_(d, c)), (mul_(c, a))));
	assert(eq_(temp_80_0, temp_80_1)) by {
		cong_mul_(mul_(d, c), mul_(a, c), mul_(d, c), mul_(c, a));
		lemma_mul_comm(a, c);
		lemma_eq_ref(mul_(d, c));
	}
	let temp_81_0 = (sub_((mul_(c, a)), (mul_(b, b))));
	let temp_81_1 = (sub_((mul_(a, c)), (mul_(b, b))));
	assert(eq_(temp_81_0, temp_81_1)) by {
		cong_sub_(mul_(c, a), mul_(b, b), mul_(a, c), mul_(b, b));
		lemma_mul_comm(c, a);
		lemma_mul_comm(b, b);
	}
	let temp_82_0 = (mod_((mul_((sub_(c, b)), (mul_(b, b)))), m));
	let temp_82_1 = (mod_((sub_((mul_((sub_(c, b)), (mul_(b, b)))), (mul_((mul_((mul_(d, c)), (mod_((sub_((mod_(d, m)), b)), m)))), m)))), m));
	assert(eq_(temp_82_0, temp_82_1)) by {
		lemma_mod_mul_vanish(mul_(sub_(c, b), mul_(b, b)), mul_(mul_(d, c), mod_(sub_(mod_(d, m), b), m)), m);
	}
	let temp_83_0 = (add_((mod_((mul_(c, a)), m)), (mul_(a, c))));
	let temp_83_1 = (add_((mod_((mul_(c, a)), m)), (mul_(c, a))));
	assert(eq_(temp_83_0, temp_83_1)) by {
		cong_add_(mod_(mul_(c, a), m), mul_(a, c), mod_(mul_(c, a), m), mul_(c, a));
		lemma_mul_comm(a, c);
		lemma_eq_ref(mod_(mul_(c, a), m));
	}
	let temp_84_0 = (mul_((mul_(as_elem(53), d)), (mul_(a, (mod_(b, m))))));
	let temp_84_1 = (mul_((mul_(d, as_elem(53))), (mul_(a, (mod_(b, m))))));
	assert(eq_(temp_84_0, temp_84_1)) by {
		lemma_mul_comm(as_elem(53), d);
		cong_mul_(mul_(as_elem(53), d), mul_(a, mod_(b, m)), mul_(d, as_elem(53)), mul_(a, mod_(b, m)));
		lemma_eq_ref(mul_(a, mod_(b, m)));
	}
	let temp_85_0 = (mul_((sub_(as_elem(41), d)), (mod_((mul_(c, (mod_(a, m)))), m))));
	let temp_85_1 = (mul_((sub_(as_elem(41), d)), (mod_((mul_((mod_(a, m)), c)), m))));
	assert(eq_(temp_85_0, temp_85_1)) by {
		lemma_mul_comm(c, mod_(a, m));
		cong_mul_(sub_(as_elem(41), d), mod_(mul_(c, mod_(a, m)), m), sub_(as_elem(41), d), mod_(mul_(mod_(a, m), c), m));
		lemma_eq_ref(sub_(as_elem(41), d));
		cong_mod_(mul_(c, mod_(a, m)), m, mul_(mod_(a, m), c), m);
		lemma_eq_ref(m);
	}
	let temp_86_0 = (mul_((mul_((mod_(c, m)), d)), (mul_((mod_(a, m)), d))));
	let temp_86_1 = (mul_((mul_((mod_(a, m)), d)), (mul_((mod_(c, m)), d))));
	assert(eq_(temp_86_0, temp_86_1)) by {
		lemma_mul_comm(mul_(mod_(c, m), d), mul_(mod_(a, m), d));
	}
	let temp_87_0 = (mod_((mul_((mod_((mul_(a, c)), m)), (mod_((mul_(d, b)), m)))), m));
	let temp_87_1 = (mod_((mul_((mod_((mul_(d, b)), m)), (mod_((mul_(a, c)), m)))), m));
	assert(eq_(temp_87_0, temp_87_1)) by {
		lemma_mul_comm(mod_(mul_(a, c), m), mod_(mul_(d, b), m));
		cong_mod_(mul_(mod_(mul_(a, c), m), mod_(mul_(d, b), m)), m, mul_(mod_(mul_(d, b), m), mod_(mul_(a, c), m)), m);
		lemma_eq_ref(m);
	}
	let temp_88_0 = (sub_((mul_(d, b)), (mul_(a, (mod_(a, m))))));
	let temp_88_1 = (sub_((mul_(d, b)), (mul_(a, (mod_((add_((mul_((sub_((mul_(d, a)), (mul_(d, a)))), m)), a)), m))))));
	assert(eq_(temp_88_0, temp_88_1)) by {
		lemma_eq_ref(mul_(d, b));
		cong_mul_(a, mod_(a, m), a, mod_(add_(mul_(sub_(mul_(d, a), mul_(d, a)), m), a), m));
		lemma_eq_ref(a);
		lemma_mod_mul_vanish(a, sub_(mul_(d, a), mul_(d, a)), m);
		cong_sub_(mul_(d, b), mul_(a, mod_(a, m)), mul_(d, b), mul_(a, mod_(add_(mul_(sub_(mul_(d, a), mul_(d, a)), m), a), m)));
	}
	let temp_89_0 = (mul_((mul_(c, c)), (mul_((mod_(d, m)), b))));
	let temp_89_1 = (mul_(c, (mul_(c, (mul_((mod_(d, m)), b))))));
	assert(eq_(temp_89_0, temp_89_1)) by {
		lemma_mul_assoc(c, c, mul_(mod_(d, m), b));
		lemma_eq_sym(temp_89_1, temp_89_0);
	}
	let temp_90_0 = (mod_((mul_((mod_((mul_(a, c)), m)), (add_(c, d)))), m));
	let temp_90_1 = (mod_((add_((mul_((mod_((mul_(a, c)), m)), c)), (mul_((mod_((mul_(a, c)), m)), d)))), m));
	assert(eq_(temp_90_0, temp_90_1)) by {
		lemma_mul_dist(mod_(mul_(a, c), m), c, d);
		cong_mod_(mul_(mod_(mul_(a, c), m), add_(c, d)), m, add_(mul_(mod_(mul_(a, c), m), c), mul_(mod_(mul_(a, c), m), d)), m);
		lemma_eq_ref(m);
	}
	let temp_91_0 = (mul_((mul_((mod_(b, m)), b)), (mul_(c, d))));
	let temp_91_1 = (mul_((mul_(c, d)), (mul_((mod_(b, m)), b))));
	assert(eq_(temp_91_0, temp_91_1)) by {
		lemma_mul_comm(mul_(mod_(b, m), b), mul_(c, d));
	}
	let temp_92_0 = (mul_((mul_(d, (mod_(d, m)))), (mul_(a, d))));
	let temp_92_1 = (mul_(d, (mul_((mod_(d, m)), (mul_(a, d))))));
	assert(eq_(temp_92_0, temp_92_1)) by {
		lemma_eq_sym(temp_92_1, temp_92_0);
		lemma_mul_assoc(d, mod_(d, m), mul_(a, d));
	}
	let temp_93_0 = (mul_((mul_(b, d)), (mul_(d, c))));
	let temp_93_1 = (mul_((mul_(b, d)), (mul_(c, d))));
	assert(eq_(temp_93_0, temp_93_1)) by {
		cong_mul_(mul_(b, d), mul_(d, c), mul_(b, d), mul_(c, d));
		lemma_mul_comm(d, c);
		lemma_eq_ref(mul_(b, d));
	}
	let temp_94_0 = (mul_((mul_(c, c)), (mul_(a, d))));
	let temp_94_1 = (mul_(c, (mul_(c, (mul_(a, d))))));
	assert(eq_(temp_94_0, temp_94_1)) by {
		lemma_eq_sym(temp_94_1, temp_94_0);
		lemma_mul_assoc(c, c, mul_(a, d));
	}
	let temp_95_0 = (mul_((mul_(c, (mod_(b, m)))), d));
	let temp_95_1 = (mul_((mul_((mod_(b, m)), c)), d));
	assert(eq_(temp_95_0, temp_95_1)) by {
		cong_mul_(mul_(c, mod_(b, m)), d, mul_(mod_(b, m), c), d);
		lemma_mul_comm(c, mod_(b, m));
		lemma_eq_ref(d);
	}
	let temp_96_0 = (mul_((sub_(d, c)), (add_(d, b))));
	let temp_96_1 = (mul_((sub_(d, c)), (add_(b, d))));
	assert(eq_(temp_96_0, temp_96_1)) by {
		cong_mul_(sub_(d, c), add_(d, b), sub_(d, c), add_(b, d));
		lemma_add_comm(d, b);
		lemma_eq_ref(sub_(d, c));
	}
	let temp_97_0 = (mul_((mul_((mod_(d, m)), a)), (mul_(c, a))));
	let temp_97_1 = (mul_((mul_((mod_((add_(d, (mul_((add_((add_(d, c)), (mul_(a, b)))), m)))), m)), a)), (mul_(c, a))));
	assert(eq_(temp_97_0, temp_97_1)) by {
		cong_mul_(mod_(d, m), a, mod_(add_(d, mul_(add_(add_(d, c), mul_(a, b)), m)), m), a);
		lemma_eq_ref(mul_(c, a));
		lemma_eq_ref(a);
		lemma_mod_mul_vanish(d, add_(add_(d, c), mul_(a, b)), m);
		cong_mul_(mul_(mod_(d, m), a), mul_(c, a), mul_(mod_(add_(d, mul_(add_(add_(d, c), mul_(a, b)), m)), m), a), mul_(c, a));
	}
	let temp_98_0 = (mul_((mul_(b, d)), (mul_(b, b))));
	let temp_98_1 = (mul_((mul_(b, d)), (mul_(b, b))));
	assert(eq_(temp_98_0, temp_98_1)) by {
		lemma_eq_ref(temp_98_0);
	}
	let temp_99_0 = (mul_((mod_((mul_(a, c)), m)), (mul_(d, d))));
	let temp_99_1 = (mul_((mul_((mod_((mul_(a, c)), m)), d)), d));
	assert(eq_(temp_99_0, temp_99_1)) by {
		lemma_mul_assoc(mod_(mul_(a, c), m), d, d);
	}
	let temp_100_0 = (sub_((mul_(a, c)), (mul_(c, c))));
	let temp_100_1 = (sub_((mul_(a, c)), (mul_(c, c))));
	assert(eq_(temp_100_0, temp_100_1)) by {
		lemma_eq_ref(temp_100_0);
	}
	let temp_101_0 = (mul_((mul_(d, (mod_(a, m)))), (add_(d, a))));
	let temp_101_1 = (mul_((mul_(d, (mod_((add_(a, (mul_((mul_((mul_(c, (mod_(b, m)))), (mul_(b, c)))), m)))), m)))), (add_(d, a))));
	assert(eq_(temp_101_0, temp_101_1)) by {
		lemma_mod_mul_vanish(a, mul_(mul_(c, mod_(b, m)), mul_(b, c)), m);
		cong_mul_(mul_(d, mod_(a, m)), add_(d, a), mul_(d, mod_(add_(a, mul_(mul_(mul_(c, mod_(b, m)), mul_(b, c)), m)), m)), add_(d, a));
		lemma_eq_ref(d);
		cong_mul_(d, mod_(a, m), d, mod_(add_(a, mul_(mul_(mul_(c, mod_(b, m)), mul_(b, c)), m)), m));
		lemma_eq_ref(add_(d, a));
	}
	let temp_102_0 = (mul_((mod_((add_(c, c)), m)), (mul_(b, b))));
	let temp_102_1 = (mul_((mul_((mod_((add_(c, c)), m)), b)), b));
	assert(eq_(temp_102_0, temp_102_1)) by {
		lemma_mul_assoc(mod_(add_(c, c), m), b, b);
	}
	let temp_103_0 = (mul_((mul_(b, b)), (mul_(b, b))));
	let temp_103_1 = (mul_((mul_(b, b)), (mul_(b, b))));
	assert(eq_(temp_103_0, temp_103_1)) by {
		lemma_eq_ref(temp_103_0);
	}
	let temp_104_0 = (mul_((mul_(d, c)), (add_(c, b))));
	let temp_104_1 = (mul_(d, (mul_(c, (add_(c, b))))));
	assert(eq_(temp_104_0, temp_104_1)) by {
		lemma_eq_sym(temp_104_1, temp_104_0);
		lemma_mul_assoc(d, c, add_(c, b));
	}
	let temp_105_0 = (add_((mul_(c, a)), (mod_((mul_(b, a)), m))));
	let temp_105_1 = (add_((mul_(c, a)), (mod_((add_((mul_(b, a)), (mul_((mul_((mul_(b, c)), (mul_(d, a)))), m)))), m))));
	assert(eq_(temp_105_0, temp_105_1)) by {
		lemma_mod_mul_vanish(mul_(b, a), mul_(mul_(b, c), mul_(d, a)), m);
		cong_add_(mul_(c, a), mod_(mul_(b, a), m), mul_(c, a), mod_(add_(mul_(b, a), mul_(mul_(mul_(b, c), mul_(d, a)), m)), m));
		lemma_eq_ref(mul_(c, a));
	}
	let temp_106_0 = (mul_((mul_((mod_(b, m)), b)), (mul_(b, d))));
	let temp_106_1 = (mul_((mul_(b, d)), (mul_((mod_(b, m)), b))));
	assert(eq_(temp_106_0, temp_106_1)) by {
		lemma_mul_comm(mul_(mod_(b, m), b), mul_(b, d));
	}
	let temp_107_0 = (add_((mul_(c, b)), (mul_(a, (mod_(a, m))))));
	let temp_107_1 = (add_((mul_(c, b)), (mul_((mod_(a, m)), a))));
	assert(eq_(temp_107_0, temp_107_1)) by {
		lemma_mul_comm(a, mod_(a, m));
		cong_add_(mul_(c, b), mul_(a, mod_(a, m)), mul_(c, b), mul_(mod_(a, m), a));
		lemma_eq_ref(mul_(c, b));
	}
	let temp_108_0 = (add_((mul_(a, c)), (mul_(b, as_elem(34)))));
	let temp_108_1 = (add_((mul_(b, as_elem(34))), (mul_(a, c))));
	assert(eq_(temp_108_0, temp_108_1)) by {
		lemma_add_comm(mul_(a, c), mul_(b, as_elem(34)));
	}
	let temp_109_0 = (mul_((sub_(b, as_elem(71))), (add_(d, b))));
	let temp_109_1 = (sub_((mul_(b, (add_(d, b)))), (mul_(as_elem(71), (add_(d, b))))));
	assert(eq_(temp_109_0, temp_109_1)) by {
		lemma_mul_dist(add_(d, b), b, as_elem(71));
	}
	let temp_110_0 = (mul_((sub_(d, d)), (mul_(b, a))));
	let temp_110_1 = (sub_((mul_(d, (mul_(b, a)))), (mul_(d, (mul_(b, a))))));
	assert(eq_(temp_110_0, temp_110_1)) by {
		lemma_mul_dist(mul_(b, a), d, d);
	}
	let temp_111_0 = (mul_((mul_(a, b)), (mul_(a, (mod_(as_elem(12), m))))));
	let temp_111_1 = (mul_(a, (mul_(b, (mul_(a, (mod_(as_elem(12), m))))))));
	assert(eq_(temp_111_0, temp_111_1)) by {
		lemma_mul_assoc(a, b, mul_(a, mod_(as_elem(12), m)));
		lemma_eq_sym(temp_111_1, temp_111_0);
	}
	let temp_112_0 = (mul_((mul_(d, b)), (mul_(d, c))));
	let temp_112_1 = (mul_(d, (mul_(b, (mul_(d, c))))));
	assert(eq_(temp_112_0, temp_112_1)) by {
		lemma_eq_sym(temp_112_1, temp_112_0);
		lemma_mul_assoc(d, b, mul_(d, c));
	}
	let temp_113_0 = (mul_((mul_(a, a)), (mul_(as_elem(9), d))));
	let temp_113_1 = (mul_((mul_(a, a)), (mul_(as_elem(9), d))));
	assert(eq_(temp_113_0, temp_113_1)) by {
		lemma_eq_ref(temp_113_0);
	}
	let temp_114_0 = (mul_((mul_(d, c)), (mul_(d, d))));
	let temp_114_1 = (mul_((mul_(c, d)), (mul_(d, d))));
	assert(eq_(temp_114_0, temp_114_1)) by {
		cong_mul_(mul_(d, c), mul_(d, d), mul_(c, d), mul_(d, d));
		lemma_mul_comm(d, c);
		lemma_mul_comm(d, d);
	}
	let temp_115_0 = (mul_((mul_(d, b)), (mul_((mod_(b, m)), a))));
	let temp_115_1 = (mul_((mul_(d, b)), (mul_(a, (mod_(b, m))))));
	assert(eq_(temp_115_0, temp_115_1)) by {
		lemma_mul_comm(mod_(b, m), a);
		cong_mul_(mul_(d, b), mul_(mod_(b, m), a), mul_(d, b), mul_(a, mod_(b, m)));
		lemma_eq_ref(mul_(d, b));
	}
	let temp_116_0 = (mul_((mod_((mul_(c, d)), m)), (mul_(d, c))));
	let temp_116_1 = (mul_((mul_((mod_((mul_(c, d)), m)), d)), c));
	assert(eq_(temp_116_0, temp_116_1)) by {
		lemma_mul_assoc(mod_(mul_(c, d), m), d, c);
	}
	let temp_117_0 = (mul_((mul_(b, b)), (sub_(d, a))));
	let temp_117_1 = (mul_((sub_(d, a)), (mul_(b, b))));
	assert(eq_(temp_117_0, temp_117_1)) by {
		lemma_mul_comm(mul_(b, b), sub_(d, a));
	}
	let temp_118_0 = (add_((mul_(d, c)), (add_(b, (mod_(d, m))))));
	let temp_118_1 = (add_((add_(b, (mod_(d, m)))), (mul_(d, c))));
	assert(eq_(temp_118_0, temp_118_1)) by {
		lemma_add_comm(mul_(d, c), add_(b, mod_(d, m)));
	}
	let temp_119_0 = (mul_((mul_(b, c)), (sub_(b, d))));
	let temp_119_1 = (mul_((mul_(c, b)), (sub_(b, d))));
	assert(eq_(temp_119_0, temp_119_1)) by {
		cong_mul_(mul_(b, c), sub_(b, d), mul_(c, b), sub_(b, d));
		lemma_mul_comm(b, c);
		lemma_eq_ref(sub_(b, d));
	}
	let temp_120_0 = (mul_((mod_((mul_(d, d)), m)), (add_(c, c))));
	let temp_120_1 = (mul_((mod_((add_((mul_(d, d)), (mul_((mul_((mul_(a, a)), (mul_((mod_(d, m)), c)))), m)))), m)), (add_(c, c))));
	assert(eq_(temp_120_0, temp_120_1)) by {
		lemma_mod_mul_vanish(mul_(d, d), mul_(mul_(a, a), mul_(mod_(d, m), c)), m);
		lemma_add_comm(c, c);
		cong_mul_(mod_(mul_(d, d), m), add_(c, c), mod_(add_(mul_(d, d), mul_(mul_(mul_(a, a), mul_(mod_(d, m), c)), m)), m), add_(c, c));
	}
	let temp_121_0 = (mul_((mul_(b, c)), (mul_(b, d))));
	let temp_121_1 = (mul_(b, (mul_(c, (mul_(b, d))))));
	assert(eq_(temp_121_0, temp_121_1)) by {
		lemma_eq_sym(temp_121_1, temp_121_0);
		lemma_mul_assoc(b, c, mul_(b, d));
	}
	let temp_122_0 = (add_((mul_(a, d)), b));
	let temp_122_1 = (add_(b, (mul_(a, d))));
	assert(eq_(temp_122_0, temp_122_1)) by {
		lemma_add_comm(mul_(a, d), b);
	}
	let temp_123_0 = (sub_((mul_(d, c)), (sub_(b, c))));
	let temp_123_1 = (sub_((mul_(c, d)), (sub_(b, c))));
	assert(eq_(temp_123_0, temp_123_1)) by {
		cong_sub_(mul_(d, c), sub_(b, c), mul_(c, d), sub_(b, c));
		lemma_mul_comm(d, c);
		lemma_eq_ref(sub_(b, c));
	}
	let temp_124_0 = (mul_((mul_(b, a)), (mod_((mul_(d, a)), m))));
	let temp_124_1 = (mul_((mul_(a, b)), (mod_((mul_(d, a)), m))));
	assert(eq_(temp_124_0, temp_124_1)) by {
		lemma_mul_comm(b, a);
		cong_mul_(mul_(b, a), mod_(mul_(d, a), m), mul_(a, b), mod_(mul_(d, a), m));
		lemma_eq_ref(mod_(mul_(d, a), m));
	}
	let temp_125_0 = (sub_((mod_((mul_((mod_(b, m)), b)), m)), (add_(a, c))));
	let temp_125_1 = (sub_((mod_((mul_((mod_(b, m)), b)), m)), (add_(c, a))));
	assert(eq_(temp_125_0, temp_125_1)) by {
		lemma_add_comm(a, c);
		cong_sub_(mod_(mul_(mod_(b, m), b), m), add_(a, c), mod_(mul_(mod_(b, m), b), m), add_(c, a));
		lemma_eq_ref(mod_(mul_(mod_(b, m), b), m));
	}
	let temp_126_0 = (mod_((mul_((mul_(c, c)), (mul_(c, b)))), m));
	let temp_126_1 = (mod_((mul_((mul_((mul_(c, c)), c)), b)), m));
	assert(eq_(temp_126_0, temp_126_1)) by {
		lemma_mul_assoc(mul_(c, c), c, b);
		cong_mod_(mul_(mul_(c, c), mul_(c, b)), m, mul_(mul_(mul_(c, c), c), b), m);
		lemma_eq_ref(m);
	}
	let temp_127_0 = (mul_((mul_(d, c)), (mul_(b, a))));
	let temp_127_1 = (mul_(d, (mul_(c, (mul_(b, a))))));
	assert(eq_(temp_127_0, temp_127_1)) by {
		lemma_eq_sym(temp_127_1, temp_127_0);
		lemma_mul_assoc(d, c, mul_(b, a));
	}
	let temp_128_0 = (mul_((sub_(b, c)), (mul_(c, c))));
	let temp_128_1 = (mul_((sub_(b, c)), (mul_(c, c))));
	assert(eq_(temp_128_0, temp_128_1)) by {
		lemma_eq_ref(temp_128_0);
	}
	let temp_129_0 = (add_((mul_(c, b)), (mul_(b, d))));
	let temp_129_1 = (add_((mul_(b, d)), (mul_(c, b))));
	assert(eq_(temp_129_0, temp_129_1)) by {
		lemma_add_comm(mul_(c, b), mul_(b, d));
	}
	let temp_130_0 = (add_((mul_(b, c)), (mul_(c, a))));
	let temp_130_1 = (add_((mul_(c, a)), (mul_(b, c))));
	assert(eq_(temp_130_0, temp_130_1)) by {
		lemma_add_comm(mul_(b, c), mul_(c, a));
	}
	let temp_131_0 = (add_((mul_(b, c)), (sub_(a, (mod_(c, m))))));
	let temp_131_1 = (add_((sub_(a, (mod_(c, m)))), (mul_(b, c))));
	assert(eq_(temp_131_0, temp_131_1)) by {
		lemma_add_comm(mul_(b, c), sub_(a, mod_(c, m)));
	}
	let temp_132_0 = (add_((mul_((mod_(c, m)), d)), (mul_(a, c))));
	let temp_132_1 = (add_((mul_((mod_((add_((mul_((mul_((add_(a, b)), (mul_(d, d)))), m)), c)), m)), d)), (mul_(a, c))));
	assert(eq_(temp_132_0, temp_132_1)) by {
		lemma_mod_mul_vanish(c, mul_(add_(a, b), mul_(d, d)), m);
		cong_add_(mul_(mod_(c, m), d), mul_(a, c), mul_(mod_(add_(mul_(mul_(add_(a, b), mul_(d, d)), m), c), m), d), mul_(a, c));
		lemma_eq_ref(d);
		cong_mul_(mod_(c, m), d, mod_(add_(mul_(mul_(add_(a, b), mul_(d, d)), m), c), m), d);
		lemma_eq_ref(mul_(a, c));
	}
	let temp_133_0 = (mul_((mul_(d, a)), (sub_((mod_(c, m)), a))));
	let temp_133_1 = (mul_((mul_(d, a)), (sub_((mod_((add_(c, (mul_((mul_((mul_((mod_(b, m)), b)), (mul_(b, c)))), m)))), m)), a))));
	assert(eq_(temp_133_0, temp_133_1)) by {
		lemma_mod_mul_vanish(c, mul_(mul_(mod_(b, m), b), mul_(b, c)), m);
		cong_mul_(mul_(d, a), sub_(mod_(c, m), a), mul_(d, a), sub_(mod_(add_(c, mul_(mul_(mul_(mod_(b, m), b), mul_(b, c)), m)), m), a));
		cong_sub_(mod_(c, m), a, mod_(add_(c, mul_(mul_(mul_(mod_(b, m), b), mul_(b, c)), m)), m), a);
		lemma_eq_ref(mul_(d, a));
		lemma_eq_ref(a);
	}
	let temp_134_0 = (mul_((mul_(b, c)), (mul_(b, c))));
	let temp_134_1 = (mul_(b, (mul_(c, (mul_(b, c))))));
	assert(eq_(temp_134_0, temp_134_1)) by {
		lemma_eq_sym(temp_134_1, temp_134_0);
		lemma_mul_assoc(b, c, mul_(b, c));
	}
	let temp_135_0 = (mod_((mul_((mul_(a, c)), (mul_(c, b)))), m));
	let temp_135_1 = (mod_((add_((mul_((sub_((mul_(a, c)), (mul_(c, a)))), m)), (mul_((mul_(a, c)), (mul_(c, b)))))), m));
	assert(eq_(temp_135_0, temp_135_1)) by {
		lemma_mod_mul_vanish(mul_(mul_(a, c), mul_(c, b)), sub_(mul_(a, c), mul_(c, a)), m);
	}

}

} // verus!