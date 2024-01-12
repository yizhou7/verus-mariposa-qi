use builtin_macros::*;
// use builtin::*;
mod nl_basics;
use crate::nl_basics::*;
verus! {

pub proof fn free_0(a: Elem, b: Elem, c: Elem, d: Elem, m: Elem)
{
	let temp_0_0 = (add_((sub_(d, a)), (mul_(b, c))));
	let temp_0_1 = (add_((mul_(b, c)), (sub_(d, a))));
	assert(eq_(temp_0_0, temp_0_1)) by {
		lemma_add_comm(sub_(d, a), mul_(b, c));
	}
	let temp_1_0 = (mul_((mul_(d, d)), (mul_(b, b))));
	let temp_1_1 = (mul_((mul_(b, b)), (mul_(d, d))));
	assert(eq_(temp_1_0, temp_1_1)) by {
		lemma_mul_comm(mul_(d, d), mul_(b, b));
	}
	let temp_2_0 = (mod_((mul_((mul_(c, c)), (mul_(d, b)))), m));
	let temp_2_1 = (mod_((sub_((mul_((mul_(c, c)), (mul_(d, b)))), (mul_((mul_((mul_((mod_(d, m)), as_elem(54))), (mul_((mod_(c, m)), d)))), m)))), m));
	assert(eq_(temp_2_0, temp_2_1)) by {
		lemma_mod_mul_vanish(mul_(mul_(c, c), mul_(d, b)), mul_(mul_(mod_(d, m), as_elem(54)), mul_(mod_(c, m), d)), m);
	}
	let temp_3_0 = (add_((mod_((mul_((mod_(b, m)), b)), m)), (mul_(c, a))));
	let temp_3_1 = (add_((mul_(c, a)), (mod_((mul_((mod_(b, m)), b)), m))));
	assert(eq_(temp_3_0, temp_3_1)) by {
		lemma_add_comm(mod_(mul_(mod_(b, m), b), m), mul_(c, a));
	}
	let temp_4_0 = (mul_((mul_(a, b)), (mod_((mul_(c, d)), m))));
	let temp_4_1 = (mul_((mul_(a, b)), (mod_((sub_((mul_(c, d)), (mul_((mul_((mod_((mul_(b, (mod_(b, m)))), m)), (add_(d, d)))), m)))), m))));
	assert(eq_(temp_4_0, temp_4_1)) by {
		lemma_mod_mul_vanish(mul_(c, d), mul_(mod_(mul_(b, mod_(b, m)), m), add_(d, d)), m);
		cong_mul_(mul_(a, b), mod_(mul_(c, d), m), mul_(a, b), mod_(sub_(mul_(c, d), mul_(mul_(mod_(mul_(b, mod_(b, m)), m), add_(d, d)), m)), m));
		lemma_eq_ref(mul_(a, b));
	}
	let temp_5_0 = (mul_((add_(c, a)), (mul_(a, (mod_(c, m))))));
	let temp_5_1 = (mul_((add_(a, c)), (mul_(a, (mod_(c, m))))));
	assert(eq_(temp_5_0, temp_5_1)) by {
		lemma_add_comm(c, a);
		cong_mul_(add_(c, a), mul_(a, mod_(c, m)), add_(a, c), mul_(a, mod_(c, m)));
		lemma_eq_ref(mul_(a, mod_(c, m)));
	}
	let temp_6_0 = (mul_((mul_((mod_(b, m)), c)), (mul_(d, b))));
	let temp_6_1 = (mul_((mul_((mod_((add_(b, (mul_((sub_((mul_(a, b)), (mul_(c, c)))), m)))), m)), c)), (mul_(d, b))));
	assert(eq_(temp_6_0, temp_6_1)) by {
		cong_mul_(mod_(b, m), c, mod_(add_(b, mul_(sub_(mul_(a, b), mul_(c, c)), m)), m), c);
		lemma_eq_ref(mul_(d, b));
		lemma_eq_ref(c);
		lemma_mod_mul_vanish(b, sub_(mul_(a, b), mul_(c, c)), m);
		cong_mul_(mul_(mod_(b, m), c), mul_(d, b), mul_(mod_(add_(b, mul_(sub_(mul_(a, b), mul_(c, c)), m)), m), c), mul_(d, b));
	}
	let temp_7_0 = (mul_((mod_((mul_(as_elem(51), d)), m)), (mul_(c, b))));
	let temp_7_1 = (mul_((mul_((mod_((mul_(as_elem(51), d)), m)), c)), b));
	assert(eq_(temp_7_0, temp_7_1)) by {
		lemma_mul_assoc(mod_(mul_(as_elem(51), d), m), c, b);
	}
	let temp_8_0 = (mod_((mul_((sub_((mod_(c, m)), d)), d)), m));
	let temp_8_1 = (mod_((sub_((mul_((sub_((mod_(c, m)), d)), d)), (mul_((mul_((mul_(b, as_elem(85))), (mul_((mod_(c, m)), d)))), m)))), m));
	assert(eq_(temp_8_0, temp_8_1)) by {
		lemma_mod_mul_vanish(mul_(sub_(mod_(c, m), d), d), mul_(mul_(b, as_elem(85)), mul_(mod_(c, m), d)), m);
	}
	let temp_9_0 = (mul_((add_(d, (mod_(d, m)))), (mod_((mul_(b, a)), m))));
	let temp_9_1 = (mul_((add_((mod_(d, m)), d)), (mod_((mul_(b, a)), m))));
	assert(eq_(temp_9_0, temp_9_1)) by {
		lemma_add_comm(d, mod_(d, m));
		cong_mul_(add_(d, mod_(d, m)), mod_(mul_(b, a), m), add_(mod_(d, m), d), mod_(mul_(b, a), m));
		lemma_eq_ref(mod_(mul_(b, a), m));
	}
	let temp_10_0 = (add_((mul_(d, c)), (mod_((mul_(c, (mod_(a, m)))), m))));
	let temp_10_1 = (add_((mul_(d, c)), (mod_((mod_((mul_(c, a)), m)), m))));
	assert(eq_(temp_10_0, temp_10_1)) by {
		lemma_mod_mul_noop(c, a, m);
		cong_add_(mul_(d, c), mod_(mul_(c, mod_(a, m)), m), mul_(d, c), mod_(mod_(mul_(c, a), m), m));
		lemma_eq_sym(mod_(mod_(mul_(c, a), m), m), mod_(mul_(c, mod_(a, m)), m));
		lemma_eq_ref(mul_(d, c));
	}
	let temp_11_0 = (add_((mul_(d, d)), (mul_((mod_(b, m)), d))));
	let temp_11_1 = (add_((mul_((mod_(b, m)), d)), (mul_(d, d))));
	assert(eq_(temp_11_0, temp_11_1)) by {
		lemma_add_comm(mul_(d, d), mul_(mod_(b, m), d));
	}
	let temp_12_0 = (mul_((mul_(c, d)), (mod_((mul_(a, a)), m))));
	let temp_12_1 = (mul_((mul_(d, c)), (mod_((mul_(a, a)), m))));
	assert(eq_(temp_12_0, temp_12_1)) by {
		lemma_mul_comm(c, d);
		cong_mul_(mul_(c, d), mod_(mul_(a, a), m), mul_(d, c), mod_(mul_(a, a), m));
		lemma_eq_ref(mod_(mul_(a, a), m));
	}
	let temp_13_0 = (mul_((mod_((mul_(c, d)), m)), (mul_(d, (mod_(d, m))))));
	let temp_13_1 = (mul_((mul_((mod_((mul_(c, d)), m)), d)), (mod_(d, m))));
	assert(eq_(temp_13_0, temp_13_1)) by {
		lemma_mul_assoc(mod_(mul_(c, d), m), d, mod_(d, m));
	}
	let temp_14_0 = (sub_((mul_(d, b)), (mul_(b, b))));
	let temp_14_1 = (mul_((sub_(d, b)), b));
	assert(eq_(temp_14_0, temp_14_1)) by {
		lemma_eq_sym(temp_14_1, temp_14_0);
		lemma_mul_dist(b, d, b);
	}
	let temp_15_0 = (mul_((mul_(a, c)), (mul_(c, a))));
	let temp_15_1 = (mul_((mul_(c, a)), (mul_(a, c))));
	assert(eq_(temp_15_0, temp_15_1)) by {
		lemma_mul_comm(mul_(a, c), mul_(c, a));
	}
	let temp_16_0 = (mul_((sub_(d, a)), (mul_(c, c))));
	let temp_16_1 = (sub_((mul_(d, (mul_(c, c)))), (mul_(a, (mul_(c, c))))));
	assert(eq_(temp_16_0, temp_16_1)) by {
		lemma_mul_dist(mul_(c, c), d, a);
	}
	let temp_17_0 = (mul_((mul_((mod_(c, m)), b)), (mul_(c, (mod_(b, m))))));
	let temp_17_1 = (mul_((mul_(c, (mod_(b, m)))), (mul_((mod_(c, m)), b))));
	assert(eq_(temp_17_0, temp_17_1)) by {
		lemma_mul_comm(mul_(mod_(c, m), b), mul_(c, mod_(b, m)));
	}
	let temp_18_0 = (mul_((mul_((mod_(c, m)), c)), (mul_(a, as_elem(48)))));
	let temp_18_1 = (mul_((mul_((mod_((add_((mul_((mul_((sub_(b, a)), (mul_(d, b)))), m)), c)), m)), c)), (mul_(a, as_elem(48)))));
	assert(eq_(temp_18_0, temp_18_1)) by {
		lemma_mul_comm(as_elem(48), a);
		lemma_mul_comm(a, as_elem(48));
		lemma_mod_mul_vanish(c, mul_(sub_(b, a), mul_(d, b)), m);
		cong_mul_(mul_(mod_(c, m), c), mul_(a, as_elem(48)), mul_(mod_(add_(mul_(mul_(sub_(b, a), mul_(d, b)), m), c), m), c), mul_(a, as_elem(48)));
		lemma_eq_ref(c);
		lemma_eq_trans(mul_(a, as_elem(48)), mul_(as_elem(48), a), mul_(a, as_elem(48)));
		cong_mul_(mod_(c, m), c, mod_(add_(mul_(mul_(sub_(b, a), mul_(d, b)), m), c), m), c);
	}
	let temp_19_0 = (mul_((add_(a, d)), (mul_(c, as_elem(84)))));
	let temp_19_1 = (add_((mul_(a, (mul_(c, as_elem(84))))), (mul_(d, (mul_(c, as_elem(84)))))));
	assert(eq_(temp_19_0, temp_19_1)) by {
		lemma_mul_dist(a, d, mul_(c, as_elem(84)));
	}
	let temp_20_0 = (add_((mul_(d, (mod_(b, m)))), (mod_((mul_((mod_(b, m)), d)), m))));
	let temp_20_1 = (add_((mul_(d, (mod_(b, m)))), (mod_((sub_((mul_((mod_(b, m)), d)), (mul_((mul_((mul_(c, (mod_(c, m)))), (mod_((mul_(a, b)), m)))), m)))), m))));
	assert(eq_(temp_20_0, temp_20_1)) by {
		lemma_eq_ref(mul_(d, mod_(b, m)));
		cong_add_(mul_(d, mod_(b, m)), mod_(mul_(mod_(b, m), d), m), mul_(d, mod_(b, m)), mod_(sub_(mul_(mod_(b, m), d), mul_(mul_(mul_(c, mod_(c, m)), mod_(mul_(a, b), m)), m)), m));
		lemma_mod_mul_vanish(mul_(mod_(b, m), d), mul_(mul_(c, mod_(c, m)), mod_(mul_(a, b), m)), m);
	}
	let temp_21_0 = (mul_((mul_(a, b)), (mul_(c, d))));
	let temp_21_1 = (mul_((mul_((mul_(a, b)), c)), d));
	assert(eq_(temp_21_0, temp_21_1)) by {
		lemma_mul_assoc(mul_(a, b), c, d);
	}
	let temp_22_0 = (mul_((mul_(d, a)), (mul_(c, d))));
	let temp_22_1 = (mul_((mul_(c, d)), (mul_(d, a))));
	assert(eq_(temp_22_0, temp_22_1)) by {
		lemma_mul_comm(mul_(d, a), mul_(c, d));
	}
	let temp_23_0 = (mul_((add_(a, (mod_(b, m)))), (mod_((sub_(a, c)), m))));
	let temp_23_1 = (mul_((mod_((sub_(a, c)), m)), (add_(a, (mod_(b, m))))));
	assert(eq_(temp_23_0, temp_23_1)) by {
		lemma_mul_comm(add_(a, mod_(b, m)), mod_(sub_(a, c), m));
	}
	let temp_24_0 = (mul_((mul_(c, c)), (mod_((mul_((mod_(b, m)), a)), m))));
	let temp_24_1 = (mul_((mul_(c, c)), (mod_((mul_((mod_(b, m)), a)), m))));
	assert(eq_(temp_24_0, temp_24_1)) by {
		lemma_eq_ref(temp_24_0);
	}
	let temp_25_0 = (mul_((sub_(c, c)), (mul_(b, a))));
	let temp_25_1 = (sub_((mul_(c, (mul_(b, a)))), (mul_(c, (mul_(b, a))))));
	assert(eq_(temp_25_0, temp_25_1)) by {
		lemma_mul_dist(mul_(b, a), c, c);
	}
	let temp_26_0 = (mod_((mul_((mul_(a, (mod_(d, m)))), (add_(a, d)))), m));
	let temp_26_1 = (mod_((add_((mul_((mul_(a, (mod_(d, m)))), a)), (mul_((mul_(a, (mod_(d, m)))), d)))), m));
	assert(eq_(temp_26_0, temp_26_1)) by {
		lemma_mul_dist(mul_(a, mod_(d, m)), a, d);
		cong_mod_(mul_(mul_(a, mod_(d, m)), add_(a, d)), m, add_(mul_(mul_(a, mod_(d, m)), a), mul_(mul_(a, mod_(d, m)), d)), m);
		lemma_eq_ref(m);
	}
	let temp_27_0 = (mul_((mul_(d, as_elem(37))), (mul_(d, b))));
	let temp_27_1 = (mul_((mul_((mul_(d, as_elem(37))), d)), b));
	assert(eq_(temp_27_0, temp_27_1)) by {
		lemma_mul_assoc(mul_(d, as_elem(37)), d, b);
	}
	let temp_28_0 = (mul_((mod_((mul_(d, a)), m)), (mul_(c, b))));
	let temp_28_1 = (mul_((mul_(c, b)), (mod_((mul_(d, a)), m))));
	assert(eq_(temp_28_0, temp_28_1)) by {
		lemma_mul_comm(mod_(mul_(d, a), m), mul_(c, b));
	}
	let temp_29_0 = (mul_((mul_(b, b)), (add_(c, b))));
	let temp_29_1 = (mul_((mul_(b, b)), (add_(b, c))));
	assert(eq_(temp_29_0, temp_29_1)) by {
		cong_mul_(mul_(b, b), add_(c, b), mul_(b, b), add_(b, c));
		lemma_add_comm(c, b);
		lemma_mul_comm(b, b);
	}
	let temp_30_0 = (sub_((mul_(a, d)), (mul_(a, b))));
	let temp_30_1 = (sub_((mul_(a, d)), (mul_(b, a))));
	assert(eq_(temp_30_0, temp_30_1)) by {
		cong_sub_(mul_(a, d), mul_(a, b), mul_(a, d), mul_(b, a));
		lemma_mul_comm(a, b);
		lemma_eq_ref(mul_(a, d));
	}
	let temp_31_0 = (mul_((mul_(a, b)), (mul_(d, d))));
	let temp_31_1 = (mul_((mul_((mul_(a, b)), d)), d));
	assert(eq_(temp_31_0, temp_31_1)) by {
		lemma_mul_assoc(mul_(a, b), d, d);
	}
	let temp_32_0 = (sub_((add_(d, c)), (mul_(b, c))));
	let temp_32_1 = (sub_((add_(d, c)), (mul_(c, b))));
	assert(eq_(temp_32_0, temp_32_1)) by {
		cong_sub_(add_(d, c), mul_(b, c), add_(d, c), mul_(c, b));
		lemma_mul_comm(b, c);
		lemma_eq_ref(add_(d, c));
	}
	let temp_33_0 = (mul_((sub_(a, a)), (mul_(a, c))));
	let temp_33_1 = (sub_((mul_(a, (mul_(a, c)))), (mul_(a, (mul_(a, c))))));
	assert(eq_(temp_33_0, temp_33_1)) by {
		lemma_mul_dist(mul_(a, c), a, a);
	}
	let temp_34_0 = (add_((mul_(c, d)), (mul_(d, (mod_(b, m))))));
	let temp_34_1 = (add_((mul_(d, (mod_(b, m)))), (mul_(c, d))));
	assert(eq_(temp_34_0, temp_34_1)) by {
		lemma_add_comm(mul_(c, d), mul_(d, mod_(b, m)));
	}
	let temp_35_0 = (mul_((mul_(a, d)), (sub_(c, c))));
	let temp_35_1 = (mul_(a, (mul_(d, (sub_(c, c))))));
	assert(eq_(temp_35_0, temp_35_1)) by {
		lemma_eq_sym(temp_35_1, temp_35_0);
		lemma_mul_assoc(a, d, sub_(c, c));
	}
	let temp_36_0 = (mul_((add_(b, a)), (mul_(d, b))));
	let temp_36_1 = (mul_((mul_((add_(b, a)), d)), b));
	assert(eq_(temp_36_0, temp_36_1)) by {
		lemma_mul_assoc(add_(b, a), d, b);
	}
	let temp_37_0 = (add_((mul_((mod_(c, m)), d)), (mul_(c, b))));
	let temp_37_1 = (add_((mul_(c, b)), (mul_((mod_(c, m)), d))));
	assert(eq_(temp_37_0, temp_37_1)) by {
		lemma_add_comm(mul_(mod_(c, m), d), mul_(c, b));
	}
	let temp_38_0 = (mod_((mul_((mul_(as_elem(6), a)), (mul_(d, a)))), m));
	let temp_38_1 = (mod_((mul_(as_elem(6), (mul_(a, (mul_(d, a)))))), m));
	assert(eq_(temp_38_0, temp_38_1)) by {
		lemma_mul_assoc(as_elem(6), a, mul_(d, a));
		cong_mod_(mul_(mul_(as_elem(6), a), mul_(d, a)), m, mul_(as_elem(6), mul_(a, mul_(d, a))), m);
		lemma_eq_sym(mul_(as_elem(6), mul_(a, mul_(d, a))), mul_(mul_(as_elem(6), a), mul_(d, a)));
		lemma_eq_ref(m);
	}
	let temp_39_0 = (add_((sub_(b, as_elem(90))), (mod_((mul_((mod_(b, m)), b)), m))));
	let temp_39_1 = (add_((sub_(b, as_elem(90))), (mod_((mul_((mod_((add_(b, (mul_((mul_((mul_(c, a)), (mul_(a, c)))), m)))), m)), b)), m))));
	assert(eq_(temp_39_0, temp_39_1)) by {
		cong_add_(sub_(b, as_elem(90)), mod_(mul_(mod_(b, m), b), m), sub_(b, as_elem(90)), mod_(mul_(mod_(add_(b, mul_(mul_(mul_(c, a), mul_(a, c)), m)), m), b), m));
		lemma_mod_mul_vanish(b, mul_(mul_(c, a), mul_(a, c)), m);
		lemma_eq_ref(sub_(b, as_elem(90)));
		cong_mod_(mul_(mod_(b, m), b), m, mul_(mod_(add_(b, mul_(mul_(mul_(c, a), mul_(a, c)), m)), m), b), m);
		cong_mul_(mod_(b, m), b, mod_(add_(b, mul_(mul_(mul_(c, a), mul_(a, c)), m)), m), b);
		lemma_eq_ref(m);
		lemma_eq_ref(b);
	}
	let temp_40_0 = (mul_((mul_(c, a)), (sub_(d, c))));
	let temp_40_1 = (mul_((sub_(d, c)), (mul_(c, a))));
	assert(eq_(temp_40_0, temp_40_1)) by {
		lemma_mul_comm(mul_(c, a), sub_(d, c));
	}
	let temp_41_0 = (add_((mul_(d, a)), (mul_(a, d))));
	let temp_41_1 = (add_((mul_(a, d)), (mul_(d, a))));
	assert(eq_(temp_41_0, temp_41_1)) by {
		lemma_add_comm(mul_(d, a), mul_(a, d));
	}
	let temp_42_0 = (add_((mul_(c, c)), (mul_(b, b))));
	let temp_42_1 = (add_((mul_(b, b)), (mul_(c, c))));
	assert(eq_(temp_42_0, temp_42_1)) by {
		lemma_add_comm(mul_(c, c), mul_(b, b));
	}
	let temp_43_0 = (mul_((mul_(c, c)), (mul_(c, d))));
	let temp_43_1 = (mul_(c, (mul_(c, (mul_(c, d))))));
	assert(eq_(temp_43_0, temp_43_1)) by {
		lemma_eq_sym(temp_43_1, temp_43_0);
		lemma_mul_assoc(c, c, mul_(c, d));
	}
	let temp_44_0 = (sub_((mul_(a, c)), (mod_((mul_(a, a)), m))));
	let temp_44_1 = (sub_((mul_(a, c)), (mod_((mul_(a, a)), m))));
	assert(eq_(temp_44_0, temp_44_1)) by {
		lemma_eq_ref(temp_44_0);
	}
	let temp_45_0 = (mul_((mul_(a, b)), (mul_(b, a))));
	let temp_45_1 = (mul_((mul_(b, a)), (mul_(a, b))));
	assert(eq_(temp_45_0, temp_45_1)) by {
		lemma_mul_comm(mul_(a, b), mul_(b, a));
	}
	let temp_46_0 = (mul_((mul_(d, b)), (mul_(b, c))));
	let temp_46_1 = (mul_((mul_((mul_(d, b)), b)), c));
	assert(eq_(temp_46_0, temp_46_1)) by {
		lemma_mul_assoc(mul_(d, b), b, c);
	}
	let temp_47_0 = (mul_((mul_(a, (mod_(a, m)))), (mul_((mod_(a, m)), b))));
	let temp_47_1 = (mul_((mul_((mod_(a, m)), a)), (mul_((mod_(a, m)), b))));
	assert(eq_(temp_47_0, temp_47_1)) by {
		cong_mul_(mul_(a, mod_(a, m)), mul_(mod_(a, m), b), mul_(mod_(a, m), a), mul_(mod_(a, m), b));
		lemma_mul_comm(a, mod_(a, m));
		lemma_eq_ref(mul_(mod_(a, m), b));
	}
	let temp_48_0 = (mul_((add_((mod_(c, m)), d)), (mul_(a, b))));
	let temp_48_1 = (add_((mul_((mod_(c, m)), (mul_(a, b)))), (mul_(d, (mul_(a, b))))));
	assert(eq_(temp_48_0, temp_48_1)) by {
		lemma_mul_dist(mod_(c, m), d, mul_(a, b));
	}
	let temp_49_0 = (mul_((mul_(a, a)), (mul_(as_elem(82), a))));
	let temp_49_1 = (mul_((mul_((mul_(a, a)), as_elem(82))), a));
	assert(eq_(temp_49_0, temp_49_1)) by {
		lemma_mul_assoc(mul_(a, a), as_elem(82), a);
	}
	let temp_50_0 = (mod_((mul_((mul_(a, b)), (mod_((mul_(c, a)), m)))), m));
	let temp_50_1 = (mod_((mul_((mul_(a, b)), (mod_((add_((mul_((mod_((add_((mul_(d, b)), (mul_(b, d)))), m)), m)), (mul_(c, a)))), m)))), m));
	assert(eq_(temp_50_0, temp_50_1)) by {
		cong_mul_(mul_(a, b), mod_(mul_(c, a), m), mul_(a, b), mod_(add_(mul_(mod_(add_(mul_(d, b), mul_(b, d)), m), m), mul_(c, a)), m));
		lemma_eq_ref(m);
		lemma_eq_ref(mul_(a, b));
		lemma_mod_mul_vanish(mul_(c, a), mod_(add_(mul_(d, b), mul_(b, d)), m), m);
		cong_mod_(mul_(mul_(a, b), mod_(mul_(c, a), m)), m, mul_(mul_(a, b), mod_(add_(mul_(mod_(add_(mul_(d, b), mul_(b, d)), m), m), mul_(c, a)), m)), m);
	}
	let temp_51_0 = (mul_((mul_(d, c)), (add_((mod_(as_elem(84), m)), b))));
	let temp_51_1 = (mul_((mul_(d, c)), (add_((mod_((add_(as_elem(84), (mul_((add_((mul_(a, c)), (mod_((mul_(as_elem(56), a)), m)))), m)))), m)), b))));
	assert(eq_(temp_51_0, temp_51_1)) by {
		cong_mul_(mul_(d, c), add_(mod_(as_elem(84), m), b), mul_(d, c), add_(mod_(add_(as_elem(84), mul_(add_(mul_(a, c), mod_(mul_(as_elem(56), a), m)), m)), m), b));
		lemma_mod_mul_vanish(as_elem(84), add_(mul_(a, c), mod_(mul_(as_elem(56), a), m)), m);
		lemma_eq_ref(mul_(d, c));
		cong_add_(mod_(as_elem(84), m), b, mod_(add_(as_elem(84), mul_(add_(mul_(a, c), mod_(mul_(as_elem(56), a), m)), m)), m), b);
		lemma_eq_ref(b);
	}
	let temp_52_0 = (mul_((mod_((mul_(d, b)), m)), (mul_(a, d))));
	let temp_52_1 = (mul_((mul_((mod_((mul_(d, b)), m)), a)), d));
	assert(eq_(temp_52_0, temp_52_1)) by {
		lemma_mul_assoc(mod_(mul_(d, b), m), a, d);
	}
	let temp_53_0 = (mul_((mul_(b, d)), (mul_(c, c))));
	let temp_53_1 = (mul_(b, (mul_(d, (mul_(c, c))))));
	assert(eq_(temp_53_0, temp_53_1)) by {
		lemma_eq_sym(temp_53_1, temp_53_0);
		lemma_mul_assoc(b, d, mul_(c, c));
	}
	let temp_54_0 = (sub_((mul_(b, c)), (mul_(a, b))));
	let temp_54_1 = (sub_((mul_(c, b)), (mul_(a, b))));
	assert(eq_(temp_54_0, temp_54_1)) by {
		cong_sub_(mul_(b, c), mul_(a, b), mul_(c, b), mul_(a, b));
		lemma_mul_comm(b, c);
		lemma_eq_ref(mul_(a, b));
	}
	let temp_55_0 = (mul_((mod_((add_(b, (mod_(c, m)))), m)), (sub_(c, c))));
	let temp_55_1 = (mul_((mod_((sub_((add_(b, (mod_(c, m)))), (mul_((mul_((mul_(d, b)), (mul_(b, b)))), m)))), m)), (sub_(c, c))));
	assert(eq_(temp_55_0, temp_55_1)) by {
		lemma_eq_ref(sub_(c, c));
		lemma_mod_mul_vanish(add_(b, mod_(c, m)), mul_(mul_(d, b), mul_(b, b)), m);
		cong_mul_(mod_(add_(b, mod_(c, m)), m), sub_(c, c), mod_(sub_(add_(b, mod_(c, m)), mul_(mul_(mul_(d, b), mul_(b, b)), m)), m), sub_(c, c));
	}
	let temp_56_0 = (mul_((mul_(d, c)), (add_((mod_(a, m)), a))));
	let temp_56_1 = (mul_((mul_(d, c)), (add_((mod_((add_((mul_((mul_((mul_(c, a)), (mul_(c, c)))), m)), a)), m)), a))));
	assert(eq_(temp_56_0, temp_56_1)) by {
		lemma_mod_mul_vanish(a, mul_(mul_(c, a), mul_(c, c)), m);
		cong_mul_(mul_(d, c), add_(mod_(a, m), a), mul_(d, c), add_(mod_(add_(mul_(mul_(mul_(c, a), mul_(c, c)), m), a), m), a));
		lemma_eq_ref(a);
		lemma_eq_ref(mul_(d, c));
		cong_add_(mod_(a, m), a, mod_(add_(mul_(mul_(mul_(c, a), mul_(c, c)), m), a), m), a);
	}
	let temp_57_0 = (mul_((mul_(c, b)), (mul_(c, d))));
	let temp_57_1 = (mul_((mul_(c, b)), (mul_(d, c))));
	assert(eq_(temp_57_0, temp_57_1)) by {
		cong_mul_(mul_(c, b), mul_(c, d), mul_(c, b), mul_(d, c));
		lemma_mul_comm(c, d);
		lemma_eq_ref(mul_(c, b));
	}
	let temp_58_0 = (mul_((add_(c, d)), (mod_((mul_(a, d)), m))));
	let temp_58_1 = (mul_((add_(d, c)), (mod_((mul_(a, d)), m))));
	assert(eq_(temp_58_0, temp_58_1)) by {
		lemma_add_comm(c, d);
		cong_mul_(add_(c, d), mod_(mul_(a, d), m), add_(d, c), mod_(mul_(a, d), m));
		lemma_eq_ref(mod_(mul_(a, d), m));
	}
	let temp_59_0 = (sub_((mul_(b, a)), (add_(c, b))));
	let temp_59_1 = (sub_((mul_(a, b)), (add_(c, b))));
	assert(eq_(temp_59_0, temp_59_1)) by {
		cong_sub_(mul_(b, a), add_(c, b), mul_(a, b), add_(c, b));
		lemma_mul_comm(b, a);
		lemma_eq_ref(add_(c, b));
	}
	let temp_60_0 = (mul_((mod_((mul_((mod_(b, m)), b)), m)), (sub_(d, d))));
	let temp_60_1 = (mul_((mod_((mul_(b, (mod_(b, m)))), m)), (sub_(d, d))));
	assert(eq_(temp_60_0, temp_60_1)) by {
		cong_mod_(mul_(mod_(b, m), b), m, mul_(b, mod_(b, m)), m);
		lemma_eq_ref(m);
		lemma_mul_comm(mod_(b, m), b);
		cong_mul_(mod_(mul_(mod_(b, m), b), m), sub_(d, d), mod_(mul_(b, mod_(b, m)), m), sub_(d, d));
		lemma_eq_ref(sub_(d, d));
	}
	let temp_61_0 = (mul_((sub_(b, b)), (mul_(b, c))));
	let temp_61_1 = (mul_((sub_(b, b)), (mul_(c, b))));
	assert(eq_(temp_61_0, temp_61_1)) by {
		cong_mul_(sub_(b, b), mul_(b, c), sub_(b, b), mul_(c, b));
		lemma_mul_comm(b, c);
		cong_sub_(b, b, b, b);
		lemma_eq_ref(b);
	}
	let temp_62_0 = (mul_((mul_(a, d)), (mod_((mul_(b, c)), m))));
	let temp_62_1 = (mul_(a, (mul_(d, (mod_((mul_(b, c)), m))))));
	assert(eq_(temp_62_0, temp_62_1)) by {
		lemma_mul_assoc(a, d, mod_(mul_(b, c), m));
		lemma_eq_sym(temp_62_1, temp_62_0);
	}
	let temp_63_0 = (mul_((mul_(a, b)), (mul_(d, d))));
	let temp_63_1 = (mul_((mul_(a, b)), (mul_(d, d))));
	assert(eq_(temp_63_0, temp_63_1)) by {
		lemma_eq_ref(temp_63_0);
	}
	let temp_64_0 = (mul_((mul_(d, b)), (mul_(d, c))));
	let temp_64_1 = (mul_(d, (mul_(b, (mul_(d, c))))));
	assert(eq_(temp_64_0, temp_64_1)) by {
		lemma_eq_sym(temp_64_1, temp_64_0);
		lemma_mul_assoc(d, b, mul_(d, c));
	}
	let temp_65_0 = (mul_((mul_(a, c)), (mul_(c, c))));
	let temp_65_1 = (mul_((mul_(a, c)), (mul_(c, c))));
	assert(eq_(temp_65_0, temp_65_1)) by {
		lemma_eq_ref(temp_65_0);
	}
	let temp_66_0 = (mod_((add_((mul_(d, b)), (mul_(b, c)))), m));
	let temp_66_1 = (mod_((add_((mul_(b, c)), (mul_(d, b)))), m));
	assert(eq_(temp_66_0, temp_66_1)) by {
		lemma_add_comm(mul_(d, b), mul_(b, c));
		cong_mod_(add_(mul_(d, b), mul_(b, c)), m, add_(mul_(b, c), mul_(d, b)), m);
		lemma_eq_ref(m);
	}
	let temp_67_0 = (mul_((add_((mod_(a, m)), d)), (sub_(d, c))));
	let temp_67_1 = (mul_((add_(d, (mod_(a, m)))), (sub_(d, c))));
	assert(eq_(temp_67_0, temp_67_1)) by {
		lemma_add_comm(mod_(a, m), d);
		cong_mul_(add_(mod_(a, m), d), sub_(d, c), add_(d, mod_(a, m)), sub_(d, c));
		lemma_eq_ref(sub_(d, c));
	}
	let temp_68_0 = (mul_((mul_(d, a)), (mul_(d, d))));
	let temp_68_1 = (mul_((mul_(a, d)), (mul_(d, d))));
	assert(eq_(temp_68_0, temp_68_1)) by {
		cong_mul_(mul_(d, a), mul_(d, d), mul_(a, d), mul_(d, d));
		lemma_mul_comm(d, a);
		lemma_mul_comm(d, d);
	}
	let temp_69_0 = (add_((mod_((mul_(b, c)), m)), (mul_((mod_(a, m)), b))));
	let temp_69_1 = (add_((mod_((sub_((mul_(b, c)), (mul_((sub_((mul_((mod_(b, m)), c)), (add_(b, b)))), m)))), m)), (mul_((mod_(a, m)), b))));
	assert(eq_(temp_69_0, temp_69_1)) by {
		lemma_mod_mul_vanish(mul_(b, c), sub_(mul_(mod_(b, m), c), add_(b, b)), m);
		cong_add_(mod_(mul_(b, c), m), mul_(mod_(a, m), b), mod_(sub_(mul_(b, c), mul_(sub_(mul_(mod_(b, m), c), add_(b, b)), m)), m), mul_(mod_(a, m), b));
		lemma_eq_ref(mul_(mod_(a, m), b));
	}
	let temp_70_0 = (sub_((mul_((mod_(a, m)), d)), (mul_(d, c))));
	let temp_70_1 = (sub_((mul_(d, (mod_(a, m)))), (mul_(d, c))));
	assert(eq_(temp_70_0, temp_70_1)) by {
		lemma_mul_comm(mod_(a, m), d);
		cong_sub_(mul_(mod_(a, m), d), mul_(d, c), mul_(d, mod_(a, m)), mul_(d, c));
		lemma_eq_ref(mul_(d, c));
	}
	let temp_71_0 = (mul_((mod_((mul_((mod_(d, m)), b)), m)), (mul_(b, a))));
	let temp_71_1 = (mul_((mul_(b, a)), (mod_((mul_((mod_(d, m)), b)), m))));
	assert(eq_(temp_71_0, temp_71_1)) by {
		lemma_mul_comm(mod_(mul_(mod_(d, m), b), m), mul_(b, a));
	}
	let temp_72_0 = (mul_((mul_((mod_(a, m)), d)), d));
	let temp_72_1 = (mul_(d, (mul_((mod_(a, m)), d))));
	assert(eq_(temp_72_0, temp_72_1)) by {
		lemma_mul_comm(mul_(mod_(a, m), d), d);
	}
	let temp_73_0 = (add_((mul_(d, as_elem(22))), (mul_(c, a))));
	let temp_73_1 = (add_((mul_(c, a)), (mul_(d, as_elem(22)))));
	assert(eq_(temp_73_0, temp_73_1)) by {
		lemma_add_comm(mul_(d, as_elem(22)), mul_(c, a));
	}
	let temp_74_0 = (mul_((mul_(c, b)), (mul_(d, c))));
	let temp_74_1 = (mul_((mul_(d, c)), (mul_(c, b))));
	assert(eq_(temp_74_0, temp_74_1)) by {
		lemma_mul_comm(mul_(c, b), mul_(d, c));
	}
	let temp_75_0 = (mul_((mod_((add_(a, c)), m)), (mul_(a, b))));
	let temp_75_1 = (mul_((mod_((add_((mul_((mul_((mod_((mul_(d, d)), m)), (mul_(d, a)))), m)), (add_(a, c)))), m)), (mul_(a, b))));
	assert(eq_(temp_75_0, temp_75_1)) by {
		lemma_mod_mul_vanish(add_(a, c), mul_(mod_(mul_(d, d), m), mul_(d, a)), m);
		cong_mul_(mod_(add_(a, c), m), mul_(a, b), mod_(add_(mul_(mul_(mod_(mul_(d, d), m), mul_(d, a)), m), add_(a, c)), m), mul_(a, b));
		lemma_eq_ref(mul_(a, b));
	}
	let temp_76_0 = (mul_((mul_(as_elem(44), b)), (sub_(c, b))));
	let temp_76_1 = (mul_(as_elem(44), (mul_(b, (sub_(c, b))))));
	assert(eq_(temp_76_0, temp_76_1)) by {
		lemma_eq_sym(temp_76_1, temp_76_0);
		lemma_mul_assoc(as_elem(44), b, sub_(c, b));
	}
	let temp_77_0 = (add_((mul_(d, c)), (mul_(d, d))));
	let temp_77_1 = (add_((mul_(d, c)), (mul_(d, d))));
	assert(eq_(temp_77_0, temp_77_1)) by {
		lemma_eq_ref(temp_77_0);
	}
	let temp_78_0 = (mul_((mul_(d, c)), (mul_(d, c))));
	let temp_78_1 = (mul_((mul_((mul_(d, c)), d)), c));
	assert(eq_(temp_78_0, temp_78_1)) by {
		lemma_mul_assoc(mul_(d, c), d, c);
	}
	let temp_79_0 = (add_((mul_(a, b)), (mul_(c, b))));
	let temp_79_1 = (add_((mul_(b, a)), (mul_(c, b))));
	assert(eq_(temp_79_0, temp_79_1)) by {
		cong_add_(mul_(a, b), mul_(c, b), mul_(b, a), mul_(c, b));
		lemma_mul_comm(a, b);
		lemma_eq_ref(mul_(c, b));
	}
	let temp_80_0 = (mul_((add_(a, a)), (sub_(b, a))));
	let temp_80_1 = (add_((mul_(a, (sub_(b, a)))), (mul_(a, (sub_(b, a))))));
	assert(eq_(temp_80_0, temp_80_1)) by {
		lemma_mul_dist(a, a, sub_(b, a));
	}
	let temp_81_0 = (sub_((add_(b, d)), (mul_(d, (mod_(d, m))))));
	let temp_81_1 = (sub_((add_(b, d)), (mul_(d, (mod_((sub_(d, (mul_((mul_((mul_(as_elem(46), c)), (sub_(d, (mod_(d, m)))))), m)))), m))))));
	assert(eq_(temp_81_0, temp_81_1)) by {
		lemma_mod_mul_vanish(d, mul_(mul_(as_elem(46), c), sub_(d, mod_(d, m))), m);
		cong_sub_(add_(b, d), mul_(d, mod_(d, m)), add_(b, d), mul_(d, mod_(sub_(d, mul_(mul_(mul_(as_elem(46), c), sub_(d, mod_(d, m))), m)), m)));
		lemma_eq_ref(d);
		cong_mul_(d, mod_(d, m), d, mod_(sub_(d, mul_(mul_(mul_(as_elem(46), c), sub_(d, mod_(d, m))), m)), m));
		lemma_eq_ref(add_(b, d));
	}
	let temp_82_0 = (add_((sub_((mod_(b, m)), c)), (mul_(a, c))));
	let temp_82_1 = (add_((sub_((mod_(b, m)), c)), (mul_(c, a))));
	assert(eq_(temp_82_0, temp_82_1)) by {
		lemma_mul_comm(a, c);
		cong_add_(sub_(mod_(b, m), c), mul_(a, c), sub_(mod_(b, m), c), mul_(c, a));
		lemma_eq_ref(sub_(mod_(b, m), c));
	}
	let temp_83_0 = (mul_((mul_(a, as_elem(53))), (mod_((mul_(b, b)), m))));
	let temp_83_1 = (mul_((mul_(as_elem(53), a)), (mod_((mul_(b, b)), m))));
	assert(eq_(temp_83_0, temp_83_1)) by {
		lemma_mul_comm(a, as_elem(53));
		cong_mul_(mul_(a, as_elem(53)), mod_(mul_(b, b), m), mul_(as_elem(53), a), mod_(mul_(b, b), m));
		lemma_eq_ref(mod_(mul_(b, b), m));
	}
	let temp_84_0 = (mul_((add_(b, d)), (mul_(a, d))));
	let temp_84_1 = (mul_((add_(b, d)), (mul_(d, a))));
	assert(eq_(temp_84_0, temp_84_1)) by {
		cong_mul_(add_(b, d), mul_(a, d), add_(b, d), mul_(d, a));
		lemma_mul_comm(a, d);
		lemma_eq_ref(add_(b, d));
	}
	let temp_85_0 = (mul_((mul_(c, a)), (mul_(d, b))));
	let temp_85_1 = (mul_((mul_(a, c)), (mul_(d, b))));
	assert(eq_(temp_85_0, temp_85_1)) by {
		cong_mul_(mul_(c, a), mul_(d, b), mul_(a, c), mul_(d, b));
		lemma_mul_comm(c, a);
		lemma_eq_ref(mul_(d, b));
	}
	let temp_86_0 = (add_((mul_(d, c)), (mul_(a, (mod_(d, m))))));
	let temp_86_1 = (add_((mul_(c, d)), (mul_(a, (mod_(d, m))))));
	assert(eq_(temp_86_0, temp_86_1)) by {
		lemma_eq_ref(mul_(a, mod_(d, m)));
		lemma_mul_comm(d, c);
		cong_add_(mul_(d, c), mul_(a, mod_(d, m)), mul_(c, d), mul_(a, mod_(d, m)));
	}
	let temp_87_0 = (mul_((mul_(a, d)), (mul_(a, c))));
	let temp_87_1 = (mul_((mul_(a, d)), (mul_(c, a))));
	assert(eq_(temp_87_0, temp_87_1)) by {
		cong_mul_(mul_(a, d), mul_(a, c), mul_(a, d), mul_(c, a));
		lemma_mul_comm(a, c);
		lemma_eq_ref(mul_(a, d));
	}
	let temp_88_0 = (mul_((add_((mod_(b, m)), a)), (sub_(as_elem(78), b))));
	let temp_88_1 = (mul_((add_((mod_((add_((mul_((mul_((add_(c, c)), (mul_(a, d)))), m)), b)), m)), a)), (sub_(as_elem(78), b))));
	assert(eq_(temp_88_0, temp_88_1)) by {
		cong_add_(mod_(b, m), a, mod_(add_(mul_(mul_(add_(c, c), mul_(a, d)), m), b), m), a);
		lemma_eq_ref(sub_(as_elem(78), b));
		lemma_eq_ref(a);
		lemma_mod_mul_vanish(b, mul_(add_(c, c), mul_(a, d)), m);
		cong_mul_(add_(mod_(b, m), a), sub_(as_elem(78), b), add_(mod_(add_(mul_(mul_(add_(c, c), mul_(a, d)), m), b), m), a), sub_(as_elem(78), b));
	}
	let temp_89_0 = (mul_((mod_((mul_(b, c)), m)), (add_(c, a))));
	let temp_89_1 = (mul_((mod_((mul_(b, c)), m)), (add_(a, c))));
	assert(eq_(temp_89_0, temp_89_1)) by {
		lemma_add_comm(c, a);
		cong_mul_(mod_(mul_(b, c), m), add_(c, a), mod_(mul_(b, c), m), add_(a, c));
		lemma_eq_ref(mod_(mul_(b, c), m));
	}
	let temp_90_0 = (mul_((mul_(a, d)), (sub_(d, d))));
	let temp_90_1 = (mul_(a, (mul_(d, (sub_(d, d))))));
	assert(eq_(temp_90_0, temp_90_1)) by {
		lemma_eq_sym(temp_90_1, temp_90_0);
		lemma_mul_assoc(a, d, sub_(d, d));
	}
	let temp_91_0 = (mul_((mul_(b, (mod_(a, m)))), (mul_(d, (mod_(a, m))))));
	let temp_91_1 = (mul_((mul_((mul_(b, (mod_(a, m)))), d)), (mod_(a, m))));
	assert(eq_(temp_91_0, temp_91_1)) by {
		lemma_mul_assoc(mul_(b, mod_(a, m)), d, mod_(a, m));
	}
	let temp_92_0 = (mul_((mul_(b, c)), (mul_(b, (mod_(as_elem(98), m))))));
	let temp_92_1 = (mul_((mul_(b, (mod_(as_elem(98), m)))), (mul_(b, c))));
	assert(eq_(temp_92_0, temp_92_1)) by {
		lemma_mul_comm(mul_(b, c), mul_(b, mod_(as_elem(98), m)));
	}
	let temp_93_0 = (mul_((mod_((sub_(d, a)), m)), (mul_(c, b))));
	let temp_93_1 = (mul_((mod_((sub_(d, a)), m)), (mul_(b, c))));
	assert(eq_(temp_93_0, temp_93_1)) by {
		lemma_mul_comm(c, b);
		cong_mul_(mod_(sub_(d, a), m), mul_(c, b), mod_(sub_(d, a), m), mul_(b, c));
		lemma_eq_ref(mod_(sub_(d, a), m));
	}
	let temp_94_0 = (mul_((add_(b, a)), (mul_(a, a))));
	let temp_94_1 = (mul_((add_(a, b)), (mul_(a, a))));
	assert(eq_(temp_94_0, temp_94_1)) by {
		cong_mul_(add_(b, a), mul_(a, a), add_(a, b), mul_(a, a));
		lemma_add_comm(b, a);
		lemma_mul_comm(a, a);
	}
	let temp_95_0 = (add_((mul_(b, b)), (add_((mod_(c, m)), c))));
	let temp_95_1 = (add_((mul_(b, b)), (add_((mod_((add_(c, (mul_((mul_((mul_(b, d)), (add_(c, d)))), m)))), m)), c))));
	assert(eq_(temp_95_0, temp_95_1)) by {
		lemma_eq_ref(c);
		cong_add_(mod_(c, m), c, mod_(add_(c, mul_(mul_(mul_(b, d), add_(c, d)), m)), m), c);
		lemma_mod_mul_vanish(c, mul_(mul_(b, d), add_(c, d)), m);
		cong_add_(mul_(b, b), add_(mod_(c, m), c), mul_(b, b), add_(mod_(add_(c, mul_(mul_(mul_(b, d), add_(c, d)), m)), m), c));
		lemma_eq_ref(mul_(b, b));
	}
	let temp_96_0 = (mul_((mul_(b, a)), (mul_((mod_(a, m)), (mod_(d, m))))));
	let temp_96_1 = (mul_((mul_(b, a)), (mul_((mod_((add_(a, (mul_((mul_((mod_((add_(a, (mod_(c, m)))), m)), (mod_((mul_(d, c)), m)))), m)))), m)), (mod_(d, m))))));
	assert(eq_(temp_96_0, temp_96_1)) by {
		cong_mul_(mul_(b, a), mul_(mod_(a, m), mod_(d, m)), mul_(b, a), mul_(mod_(add_(a, mul_(mul_(mod_(add_(a, mod_(c, m)), m), mod_(mul_(d, c), m)), m)), m), mod_(d, m)));
		lemma_mod_mul_vanish(a, mul_(mod_(add_(a, mod_(c, m)), m), mod_(mul_(d, c), m)), m);
		lemma_eq_ref(mul_(b, a));
		cong_mul_(mod_(a, m), mod_(d, m), mod_(add_(a, mul_(mul_(mod_(add_(a, mod_(c, m)), m), mod_(mul_(d, c), m)), m)), m), mod_(d, m));
		lemma_eq_ref(mod_(d, m));
	}
	let temp_97_0 = (mul_((mul_(a, c)), (sub_(a, b))));
	let temp_97_1 = (mul_(a, (mul_(c, (sub_(a, b))))));
	assert(eq_(temp_97_0, temp_97_1)) by {
		lemma_eq_sym(temp_97_1, temp_97_0);
		lemma_mul_assoc(a, c, sub_(a, b));
	}
	let temp_98_0 = (mul_((mul_(as_elem(89), d)), (mul_(c, a))));
	let temp_98_1 = (mul_((mul_((mul_(as_elem(89), d)), c)), a));
	assert(eq_(temp_98_0, temp_98_1)) by {
		lemma_mul_assoc(mul_(as_elem(89), d), c, a);
	}
	let temp_99_0 = (mul_((mul_(b, b)), (mul_(b, d))));
	let temp_99_1 = (mul_(b, (mul_(b, (mul_(b, d))))));
	assert(eq_(temp_99_0, temp_99_1)) by {
		lemma_eq_sym(temp_99_1, temp_99_0);
		lemma_mul_assoc(b, b, mul_(b, d));
	}
	let temp_100_0 = (mul_((mul_(d, d)), (mul_((mod_(b, m)), b))));
	let temp_100_1 = (mul_((mul_(d, d)), (mul_((mod_((add_((mul_((mul_((mul_(c, d)), (mul_(b, d)))), m)), b)), m)), b))));
	assert(eq_(temp_100_0, temp_100_1)) by {
		lemma_mul_comm(d, d);
		lemma_mod_mul_vanish(b, mul_(mul_(c, d), mul_(b, d)), m);
		cong_mul_(mul_(d, d), mul_(mod_(b, m), b), mul_(d, d), mul_(mod_(add_(mul_(mul_(mul_(c, d), mul_(b, d)), m), b), m), b));
		lemma_eq_ref(b);
		cong_mul_(mod_(b, m), b, mod_(add_(mul_(mul_(mul_(c, d), mul_(b, d)), m), b), m), b);
	}
	let temp_101_0 = (mul_((mul_(d, d)), (mul_(c, d))));
	let temp_101_1 = (mul_((mul_(c, d)), (mul_(d, d))));
	assert(eq_(temp_101_0, temp_101_1)) by {
		lemma_mul_comm(mul_(d, d), mul_(c, d));
	}
	let temp_102_0 = (mul_((mul_((mod_(d, m)), a)), (mul_((mod_(b, m)), c))));
	let temp_102_1 = (mul_((mul_((mod_((sub_(d, (mul_((mul_((mul_(d, a)), (mul_(c, c)))), m)))), m)), a)), (mul_((mod_(b, m)), c))));
	assert(eq_(temp_102_0, temp_102_1)) by {
		lemma_mod_mul_vanish(d, mul_(mul_(d, a), mul_(c, c)), m);
		cong_mul_(mul_(mod_(d, m), a), mul_(mod_(b, m), c), mul_(mod_(sub_(d, mul_(mul_(mul_(d, a), mul_(c, c)), m)), m), a), mul_(mod_(b, m), c));
		lemma_eq_ref(a);
		cong_mul_(mod_(d, m), a, mod_(sub_(d, mul_(mul_(mul_(d, a), mul_(c, c)), m)), m), a);
		lemma_eq_ref(mul_(mod_(b, m), c));
	}
	let temp_103_0 = (mul_((mul_(d, c)), (mul_(a, d))));
	let temp_103_1 = (mul_((mul_(a, d)), (mul_(d, c))));
	assert(eq_(temp_103_0, temp_103_1)) by {
		lemma_mul_comm(mul_(d, c), mul_(a, d));
	}
	let temp_104_0 = (mod_((mul_((mul_(d, c)), (sub_(a, a)))), m));
	let temp_104_1 = (mod_((mul_((sub_(a, a)), (mul_(d, c)))), m));
	assert(eq_(temp_104_0, temp_104_1)) by {
		lemma_mul_comm(mul_(d, c), sub_(a, a));
		cong_mod_(mul_(mul_(d, c), sub_(a, a)), m, mul_(sub_(a, a), mul_(d, c)), m);
		lemma_eq_ref(m);
	}
	let temp_105_0 = (mul_((mul_(d, (mod_(d, m)))), (mul_(d, c))));
	let temp_105_1 = (mul_((mul_(d, (mod_((sub_(d, (mul_((mul_((add_(d, c)), (mul_(a, a)))), m)))), m)))), (mul_(d, c))));
	assert(eq_(temp_105_0, temp_105_1)) by {
		lemma_mod_mul_vanish(d, mul_(add_(d, c), mul_(a, a)), m);
		cong_mul_(mul_(d, mod_(d, m)), mul_(d, c), mul_(d, mod_(sub_(d, mul_(mul_(add_(d, c), mul_(a, a)), m)), m)), mul_(d, c));
		lemma_eq_ref(d);
		cong_mul_(d, mod_(d, m), d, mod_(sub_(d, mul_(mul_(add_(d, c), mul_(a, a)), m)), m));
		lemma_eq_ref(mul_(d, c));
	}
	let temp_106_0 = (mul_((mul_(d, b)), (mul_(c, d))));
	let temp_106_1 = (mul_((mul_(c, d)), (mul_(d, b))));
	assert(eq_(temp_106_0, temp_106_1)) by {
		lemma_mul_comm(mul_(d, b), mul_(c, d));
	}
	let temp_107_0 = (sub_((mul_(b, d)), (mul_(d, (mod_(b, m))))));
	let temp_107_1 = (sub_((mul_(b, d)), (mul_(d, (mod_((add_(b, (mul_((add_((mul_(b, c)), (mul_(d, d)))), m)))), m))))));
	assert(eq_(temp_107_0, temp_107_1)) by {
		lemma_mod_mul_vanish(b, add_(mul_(b, c), mul_(d, d)), m);
		cong_sub_(mul_(b, d), mul_(d, mod_(b, m)), mul_(b, d), mul_(d, mod_(add_(b, mul_(add_(mul_(b, c), mul_(d, d)), m)), m)));
		lemma_eq_ref(d);
		cong_mul_(d, mod_(b, m), d, mod_(add_(b, mul_(add_(mul_(b, c), mul_(d, d)), m)), m));
		lemma_eq_ref(mul_(b, d));
	}
	let temp_108_0 = (mul_((mul_(a, d)), (mul_(a, b))));
	let temp_108_1 = (mul_(a, (mul_(d, (mul_(a, b))))));
	assert(eq_(temp_108_0, temp_108_1)) by {
		lemma_eq_sym(temp_108_1, temp_108_0);
		lemma_mul_assoc(a, d, mul_(a, b));
	}
	let temp_109_0 = (mul_((mul_(c, b)), (add_(b, d))));
	let temp_109_1 = (mul_((mul_(c, b)), (add_(d, b))));
	assert(eq_(temp_109_0, temp_109_1)) by {
		cong_mul_(mul_(c, b), add_(b, d), mul_(c, b), add_(d, b));
		lemma_add_comm(b, d);
		lemma_eq_ref(mul_(c, b));
	}
	let temp_110_0 = (mul_((mul_(b, d)), (add_((mod_(as_elem(97), m)), c))));
	let temp_110_1 = (add_((mul_((mul_(b, d)), (mod_(as_elem(97), m)))), (mul_((mul_(b, d)), c))));
	assert(eq_(temp_110_0, temp_110_1)) by {
		lemma_mul_dist(mul_(b, d), mod_(as_elem(97), m), c);
	}
	let temp_111_0 = (mul_((mul_(c, a)), (mul_(a, c))));
	let temp_111_1 = (mul_((mul_(c, a)), (mul_(c, a))));
	assert(eq_(temp_111_0, temp_111_1)) by {
		cong_mul_(mul_(c, a), mul_(a, c), mul_(c, a), mul_(c, a));
		lemma_mul_comm(a, c);
		lemma_eq_ref(mul_(c, a));
	}
	let temp_112_0 = (add_((mul_(a, (mod_(b, m)))), (sub_(c, d))));
	let temp_112_1 = (add_((mul_(a, (mod_((add_((mul_((mul_((mod_((mul_(a, b)), m)), (mul_(a, a)))), m)), b)), m)))), (sub_(c, d))));
	assert(eq_(temp_112_0, temp_112_1)) by {
		cong_mul_(a, mod_(b, m), a, mod_(add_(mul_(mul_(mod_(mul_(a, b), m), mul_(a, a)), m), b), m));
		lemma_eq_ref(sub_(c, d));
		lemma_eq_ref(a);
		lemma_mod_mul_vanish(b, mul_(mod_(mul_(a, b), m), mul_(a, a)), m);
		cong_add_(mul_(a, mod_(b, m)), sub_(c, d), mul_(a, mod_(add_(mul_(mul_(mod_(mul_(a, b), m), mul_(a, a)), m), b), m)), sub_(c, d));
	}
	let temp_113_0 = (mul_((mul_(a, c)), (mul_(a, d))));
	let temp_113_1 = (mul_((mul_(a, c)), (mul_(d, a))));
	assert(eq_(temp_113_0, temp_113_1)) by {
		lemma_eq_ref(mul_(a, c));
		cong_mul_(mul_(a, c), mul_(a, d), mul_(a, c), mul_(d, a));
		lemma_mul_comm(a, d);
	}
	let temp_114_0 = (mul_((mul_((mod_(d, m)), c)), (mul_(c, d))));
	let temp_114_1 = (mul_((mod_(d, m)), (mul_(c, (mul_(c, d))))));
	assert(eq_(temp_114_0, temp_114_1)) by {
		lemma_eq_sym(temp_114_1, temp_114_0);
		lemma_mul_assoc(mod_(d, m), c, mul_(c, d));
	}
	let temp_115_0 = (mod_((mul_((mul_(a, c)), (add_(b, a)))), m));
	let temp_115_1 = (mod_((sub_((mul_((mul_(a, c)), (add_(b, a)))), (mul_((mul_((add_(d, a)), (mul_(c, d)))), m)))), m));
	assert(eq_(temp_115_0, temp_115_1)) by {
		lemma_mod_mul_vanish(mul_(mul_(a, c), add_(b, a)), mul_(add_(d, a), mul_(c, d)), m);
	}
	let temp_116_0 = (sub_((sub_(a, d)), (mul_((mod_(b, m)), b))));
	let temp_116_1 = (sub_((sub_(a, d)), (mul_(b, (mod_(b, m))))));
	assert(eq_(temp_116_0, temp_116_1)) by {
		lemma_mul_comm(mod_(b, m), b);
		cong_sub_(sub_(a, d), mul_(mod_(b, m), b), sub_(a, d), mul_(b, mod_(b, m)));
		lemma_eq_ref(sub_(a, d));
	}
	let temp_117_0 = (mod_((mul_((add_((mod_(c, m)), a)), (mul_(b, a)))), m));
	let temp_117_1 = (mod_((add_((mul_((mod_(c, m)), (mul_(b, a)))), (mul_(a, (mul_(b, a)))))), m));
	assert(eq_(temp_117_0, temp_117_1)) by {
		lemma_mul_dist(mod_(c, m), a, mul_(b, a));
		cong_mod_(mul_(add_(mod_(c, m), a), mul_(b, a)), m, add_(mul_(mod_(c, m), mul_(b, a)), mul_(a, mul_(b, a))), m);
		lemma_eq_ref(m);
	}
	let temp_118_0 = (sub_((sub_(a, b)), (mod_((mul_((mod_(a, m)), a)), m))));
	let temp_118_1 = (sub_((sub_(a, b)), (mod_((mul_((mod_((add_((mul_((add_((mul_(d, c)), (mul_(a, b)))), m)), a)), m)), a)), m))));
	assert(eq_(temp_118_0, temp_118_1)) by {
		lemma_mod_mul_vanish(a, add_(mul_(d, c), mul_(a, b)), m);
		cong_sub_(sub_(a, b), mod_(mul_(mod_(a, m), a), m), sub_(a, b), mod_(mul_(mod_(add_(mul_(add_(mul_(d, c), mul_(a, b)), m), a), m), a), m));
		cong_mod_(mul_(mod_(a, m), a), m, mul_(mod_(add_(mul_(add_(mul_(d, c), mul_(a, b)), m), a), m), a), m);
		lemma_eq_ref(sub_(a, b));
		lemma_eq_ref(a);
		cong_mul_(mod_(a, m), a, mod_(add_(mul_(add_(mul_(d, c), mul_(a, b)), m), a), m), a);
		lemma_eq_ref(m);
	}
	let temp_119_0 = (mul_((mul_(c, b)), (mul_(c, b))));
	let temp_119_1 = (mul_((mul_(c, b)), (mul_(b, c))));
	assert(eq_(temp_119_0, temp_119_1)) by {
		cong_mul_(mul_(c, b), mul_(c, b), mul_(c, b), mul_(b, c));
		lemma_mul_comm(c, b);
		lemma_eq_ref(mul_(c, b));
	}
	let temp_120_0 = (add_((mul_(c, c)), (mul_(d, c))));
	let temp_120_1 = (add_((mul_(d, c)), (mul_(c, c))));
	assert(eq_(temp_120_0, temp_120_1)) by {
		lemma_add_comm(mul_(c, c), mul_(d, c));
	}

}

} // verus!