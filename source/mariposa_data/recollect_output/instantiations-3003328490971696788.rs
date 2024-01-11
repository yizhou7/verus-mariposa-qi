use builtin_macros::*;
// use builtin::*;
mod nl_basics;
use crate::nl_basics::*;
verus! {

pub proof fn free_0(a: Elem, b: Elem, c: Elem, d: Elem, m: Elem)
{
	let temp_0_0 = (mul_((add_(b, (mod_(d, m)))), (mul_(b, c))));
	let temp_0_1 = (mul_((add_(b, (mod_(d, m)))), (mul_(c, b))));
	assert(eq_(temp_0_0, temp_0_1)) by {
		lemma_mul_comm(b, c);
		cong_mul_(add_(b, mod_(d, m)), mul_(b, c), add_(b, mod_(d, m)), mul_(c, b));
		lemma_eq_ref(add_(b, mod_(d, m)));
	}
	let temp_1_0 = (sub_((mul_(c, c)), (mul_(b, c))));
	let temp_1_1 = (mul_((sub_(c, b)), c));
	assert(eq_(temp_1_0, temp_1_1)) by {
		lemma_eq_sym(temp_1_1, temp_1_0);
		lemma_mul_dist(c, c, b);
	}
	let temp_2_0 = (mul_((sub_(d, b)), (mul_(b, c))));
	let temp_2_1 = (mul_((sub_(d, b)), (mul_(c, b))));
	assert(eq_(temp_2_0, temp_2_1)) by {
		cong_mul_(sub_(d, b), mul_(b, c), sub_(d, b), mul_(c, b));
		lemma_mul_comm(b, c);
		lemma_eq_ref(sub_(d, b));
	}
	let temp_3_0 = (mod_((mul_((mul_(a, (mod_(a, m)))), (mul_(a, a)))), m));
	let temp_3_1 = (mod_((mul_((mul_(a, (mod_((add_((mul_((mul_((sub_(b, c)), (mul_(c, (mod_(b, m)))))), m)), a)), m)))), (mul_(a, a)))), m));
	assert(eq_(temp_3_0, temp_3_1)) by {
		lemma_mul_comm(a, a);
		lemma_mod_mul_vanish(a, mul_(sub_(b, c), mul_(c, mod_(b, m))), m);
		cong_mod_(mul_(mul_(a, mod_(a, m)), mul_(a, a)), m, mul_(mul_(a, mod_(add_(mul_(mul_(sub_(b, c), mul_(c, mod_(b, m))), m), a), m)), mul_(a, a)), m);
		lemma_eq_ref(m);
		lemma_eq_ref(a);
		cong_mul_(a, mod_(a, m), a, mod_(add_(mul_(mul_(sub_(b, c), mul_(c, mod_(b, m))), m), a), m));
		cong_mul_(mul_(a, mod_(a, m)), mul_(a, a), mul_(a, mod_(add_(mul_(mul_(sub_(b, c), mul_(c, mod_(b, m))), m), a), m)), mul_(a, a));
	}
	let temp_4_0 = (mod_((mul_((mul_(b, d)), (mod_((mul_(a, c)), m)))), m));
	let temp_4_1 = (mod_((mod_((mul_((mul_(b, d)), (mul_(a, c)))), m)), m));
	assert(eq_(temp_4_0, temp_4_1)) by {
		lemma_mod_mul_noop(mul_(b, d), mul_(a, c), m);
		lemma_eq_sym(temp_4_1, temp_4_0);
	}
	let temp_5_0 = (mul_((mul_(b, a)), (mul_(b, d))));
	let temp_5_1 = (mul_(b, (mul_(a, (mul_(b, d))))));
	assert(eq_(temp_5_0, temp_5_1)) by {
		lemma_eq_sym(temp_5_1, temp_5_0);
		lemma_mul_assoc(b, a, mul_(b, d));
	}
	let temp_6_0 = (mod_((add_((sub_(b, a)), (mul_(b, d)))), m));
	let temp_6_1 = (mod_((add_((add_((sub_(b, a)), (mul_(b, d)))), (mul_((mul_((mod_((mul_(c, (mod_(a, m)))), m)), (mul_(d, b)))), m)))), m));
	assert(eq_(temp_6_0, temp_6_1)) by {
		lemma_mod_mul_vanish(add_(sub_(b, a), mul_(b, d)), mul_(mod_(mul_(c, mod_(a, m)), m), mul_(d, b)), m);
	}
	let temp_7_0 = (mul_((sub_(b, a)), (mul_(d, d))));
	let temp_7_1 = (sub_((mul_(b, (mul_(d, d)))), (mul_(a, (mul_(d, d))))));
	assert(eq_(temp_7_0, temp_7_1)) by {
		lemma_mul_dist(mul_(d, d), b, a);
	}
	let temp_8_0 = (mod_((sub_((mul_(c, c)), (mod_((mul_(c, (mod_(b, m)))), m)))), m));
	let temp_8_1 = (mod_((add_((mul_((mod_((mul_((mul_(a, a)), (mul_(d, c)))), m)), m)), (sub_((mul_(c, c)), (mod_((mul_(c, (mod_(b, m)))), m)))))), m));
	assert(eq_(temp_8_0, temp_8_1)) by {
		lemma_mod_mul_vanish(sub_(mul_(c, c), mod_(mul_(c, mod_(b, m)), m)), mod_(mul_(mul_(a, a), mul_(d, c)), m), m);
	}
	let temp_9_0 = (mul_((mul_(c, c)), (mul_((mod_(d, m)), b))));
	let temp_9_1 = (mul_(c, (mul_(c, (mul_((mod_(d, m)), b))))));
	assert(eq_(temp_9_0, temp_9_1)) by {
		lemma_mul_assoc(c, c, mul_(mod_(d, m), b));
		lemma_eq_sym(temp_9_1, temp_9_0);
	}
	let temp_10_0 = (mul_((mul_(a, a)), (sub_(a, c))));
	let temp_10_1 = (mul_(a, (mul_(a, (sub_(a, c))))));
	assert(eq_(temp_10_0, temp_10_1)) by {
		lemma_eq_sym(temp_10_1, temp_10_0);
		lemma_mul_assoc(a, a, sub_(a, c));
	}
	let temp_11_0 = (sub_((mul_(a, a)), (mul_(d, d))));
	let temp_11_1 = (sub_((mul_(a, a)), (mul_(d, d))));
	assert(eq_(temp_11_0, temp_11_1)) by {
		lemma_eq_ref(temp_11_0);
	}
	let temp_12_0 = (sub_((mul_(b, b)), (mul_(a, a))));
	let temp_12_1 = (sub_((mul_(b, b)), (mul_(a, a))));
	assert(eq_(temp_12_0, temp_12_1)) by {
		lemma_eq_ref(temp_12_0);
	}
	let temp_13_0 = (mul_(c, (mul_(c, d))));
	let temp_13_1 = (mul_((mul_(c, d)), c));
	assert(eq_(temp_13_0, temp_13_1)) by {
		lemma_mul_comm(c, mul_(c, d));
	}
	let temp_14_0 = (add_((mul_(a, d)), (mul_(b, b))));
	let temp_14_1 = (add_((mul_(b, b)), (mul_(a, d))));
	assert(eq_(temp_14_0, temp_14_1)) by {
		lemma_add_comm(mul_(a, d), mul_(b, b));
	}
	let temp_15_0 = (mul_((mul_(b, b)), (mul_(a, d))));
	let temp_15_1 = (mul_((mul_(b, b)), (mul_(d, a))));
	assert(eq_(temp_15_0, temp_15_1)) by {
		cong_mul_(mul_(b, b), mul_(a, d), mul_(b, b), mul_(d, a));
		lemma_mul_comm(b, b);
		lemma_mul_comm(a, d);
	}
	let temp_16_0 = (mul_((mul_(a, c)), (mul_(b, d))));
	let temp_16_1 = (mul_(a, (mul_(c, (mul_(b, d))))));
	assert(eq_(temp_16_0, temp_16_1)) by {
		lemma_eq_sym(temp_16_1, temp_16_0);
		lemma_mul_assoc(a, c, mul_(b, d));
	}
	let temp_17_0 = (mul_((mul_(d, d)), (mul_(d, d))));
	let temp_17_1 = (mul_((mul_(d, d)), (mul_(d, d))));
	assert(eq_(temp_17_0, temp_17_1)) by {
		lemma_eq_ref(temp_17_0);
	}
	let temp_18_0 = (mul_((mul_(c, (mod_(b, m)))), (mul_(d, (mod_(d, m))))));
	let temp_18_1 = (mul_((mul_(c, (mod_(b, m)))), (mul_((mod_(d, m)), d))));
	assert(eq_(temp_18_0, temp_18_1)) by {
		lemma_mul_comm(d, mod_(d, m));
		cong_mul_(mul_(c, mod_(b, m)), mul_(d, mod_(d, m)), mul_(c, mod_(b, m)), mul_(mod_(d, m), d));
		lemma_eq_ref(mul_(c, mod_(b, m)));
	}
	let temp_19_0 = (mul_((mul_(a, as_elem(51))), (mul_(c, a))));
	let temp_19_1 = (mul_((mul_(as_elem(51), a)), (mul_(c, a))));
	assert(eq_(temp_19_0, temp_19_1)) by {
		cong_mul_(mul_(a, as_elem(51)), mul_(c, a), mul_(as_elem(51), a), mul_(c, a));
		lemma_mul_comm(a, as_elem(51));
		lemma_eq_ref(mul_(c, a));
	}
	let temp_20_0 = (mul_((mul_(c, d)), (mul_(d, as_elem(47)))));
	let temp_20_1 = (mul_(c, (mul_(d, (mul_(d, as_elem(47)))))));
	assert(eq_(temp_20_0, temp_20_1)) by {
		lemma_eq_sym(temp_20_1, temp_20_0);
		lemma_mul_assoc(c, d, mul_(d, as_elem(47)));
	}
	let temp_21_0 = (mul_((mul_(a, a)), (mul_(c, a))));
	let temp_21_1 = (mul_((mul_((mul_(a, a)), c)), a));
	assert(eq_(temp_21_0, temp_21_1)) by {
		lemma_mul_assoc(mul_(a, a), c, a);
	}
	let temp_22_0 = (mul_((mod_((mul_(d, a)), m)), (mod_((mul_(d, b)), m))));
	let temp_22_1 = (mul_((mod_((mul_(d, a)), m)), (mod_((mul_(b, d)), m))));
	assert(eq_(temp_22_0, temp_22_1)) by {
		lemma_mul_comm(d, b);
		cong_mul_(mod_(mul_(d, a), m), mod_(mul_(d, b), m), mod_(mul_(d, a), m), mod_(mul_(b, d), m));
		lemma_eq_ref(m);
		cong_mod_(mul_(d, b), m, mul_(b, d), m);
		lemma_eq_ref(mod_(mul_(d, a), m));
	}
	let temp_23_0 = (sub_((mul_(b, b)), (mul_((mod_(d, m)), (mod_(c, m))))));
	let temp_23_1 = (sub_((mul_(b, b)), (mul_((mod_(d, m)), (mod_((add_(c, (mul_((mul_((add_(c, d)), (mul_(d, d)))), m)))), m))))));
	assert(eq_(temp_23_0, temp_23_1)) by {
		lemma_mul_comm(b, b);
		lemma_mod_mul_vanish(c, mul_(add_(c, d), mul_(d, d)), m);
		cong_sub_(mul_(b, b), mul_(mod_(d, m), mod_(c, m)), mul_(b, b), mul_(mod_(d, m), mod_(add_(c, mul_(mul_(add_(c, d), mul_(d, d)), m)), m)));
		lemma_eq_ref(mod_(d, m));
		cong_mul_(mod_(d, m), mod_(c, m), mod_(d, m), mod_(add_(c, mul_(mul_(add_(c, d), mul_(d, d)), m)), m));
	}
	let temp_24_0 = (mul_((mul_(a, c)), (mod_((mul_((mod_(c, m)), d)), m))));
	let temp_24_1 = (mul_(a, (mul_(c, (mod_((mul_((mod_(c, m)), d)), m))))));
	assert(eq_(temp_24_0, temp_24_1)) by {
		lemma_mul_assoc(a, c, mod_(mul_(mod_(c, m), d), m));
		lemma_eq_sym(temp_24_1, temp_24_0);
	}
	let temp_25_0 = (mul_((mul_(d, a)), (mul_(d, c))));
	let temp_25_1 = (mul_((mul_(a, d)), (mul_(d, c))));
	assert(eq_(temp_25_0, temp_25_1)) by {
		cong_mul_(mul_(d, a), mul_(d, c), mul_(a, d), mul_(d, c));
		lemma_mul_comm(d, a);
		lemma_eq_ref(mul_(d, c));
	}
	let temp_26_0 = (mul_((mul_(c, a)), (sub_(c, a))));
	let temp_26_1 = (mul_((mul_(a, c)), (sub_(c, a))));
	assert(eq_(temp_26_0, temp_26_1)) by {
		cong_mul_(mul_(c, a), sub_(c, a), mul_(a, c), sub_(c, a));
		lemma_mul_comm(c, a);
		lemma_eq_ref(sub_(c, a));
	}
	let temp_27_0 = (mul_((sub_(b, c)), (mul_(a, c))));
	let temp_27_1 = (sub_((mul_(b, (mul_(a, c)))), (mul_(c, (mul_(a, c))))));
	assert(eq_(temp_27_0, temp_27_1)) by {
		lemma_mul_dist(mul_(a, c), b, c);
	}
	let temp_28_0 = (mul_((mod_((mul_((mod_(a, m)), (mod_(c, m)))), m)), (add_(d, b))));
	let temp_28_1 = (mul_((mod_((mod_((mul_((mod_(a, m)), c)), m)), m)), (add_(d, b))));
	assert(eq_(temp_28_0, temp_28_1)) by {
		lemma_eq_ref(add_(d, b));
		lemma_eq_sym(mod_(mod_(mul_(mod_(a, m), c), m), m), mod_(mul_(mod_(a, m), mod_(c, m)), m));
		lemma_mod_mul_noop(mod_(a, m), c, m);
		cong_mul_(mod_(mul_(mod_(a, m), mod_(c, m)), m), add_(d, b), mod_(mod_(mul_(mod_(a, m), c), m), m), add_(d, b));
	}
	let temp_29_0 = (mod_((mul_((mod_((mul_((mod_(c, m)), a)), m)), (mul_(a, (mod_(d, m)))))), m));
	let temp_29_1 = (mod_((mul_((mul_((mod_((mul_((mod_(c, m)), a)), m)), a)), (mod_(d, m)))), m));
	assert(eq_(temp_29_0, temp_29_1)) by {
		lemma_mul_assoc(mod_(mul_(mod_(c, m), a), m), a, mod_(d, m));
		cong_mod_(mul_(mod_(mul_(mod_(c, m), a), m), mul_(a, mod_(d, m))), m, mul_(mul_(mod_(mul_(mod_(c, m), a), m), a), mod_(d, m)), m);
		lemma_eq_ref(m);
	}
	let temp_30_0 = (mul_((mul_(d, d)), (add_(c, c))));
	let temp_30_1 = (mul_((mul_(d, d)), (add_(c, c))));
	assert(eq_(temp_30_0, temp_30_1)) by {
		lemma_eq_ref(temp_30_0);
	}
	let temp_31_0 = (mul_((mul_(b, d)), (mul_(a, d))));
	let temp_31_1 = (mul_(b, (mul_(d, (mul_(a, d))))));
	assert(eq_(temp_31_0, temp_31_1)) by {
		lemma_eq_sym(temp_31_1, temp_31_0);
		lemma_mul_assoc(b, d, mul_(a, d));
	}
	let temp_32_0 = (mul_((sub_(a, b)), (mul_(c, a))));
	let temp_32_1 = (mul_((sub_(a, b)), (mul_(a, c))));
	assert(eq_(temp_32_0, temp_32_1)) by {
		cong_mul_(sub_(a, b), mul_(c, a), sub_(a, b), mul_(a, c));
		lemma_mul_comm(c, a);
		lemma_eq_ref(sub_(a, b));
	}
	let temp_33_0 = (mul_((mul_((mod_(c, m)), a)), (mul_(a, d))));
	let temp_33_1 = (mul_((mul_((mod_((add_((mul_((mul_((mul_(b, a)), (mod_((mul_(a, d)), m)))), m)), c)), m)), a)), (mul_(a, d))));
	assert(eq_(temp_33_0, temp_33_1)) by {
		lemma_mod_mul_vanish(c, mul_(mul_(b, a), mod_(mul_(a, d), m)), m);
		cong_mul_(mul_(mod_(c, m), a), mul_(a, d), mul_(mod_(add_(mul_(mul_(mul_(b, a), mod_(mul_(a, d), m)), m), c), m), a), mul_(a, d));
		lemma_eq_ref(a);
		cong_mul_(mod_(c, m), a, mod_(add_(mul_(mul_(mul_(b, a), mod_(mul_(a, d), m)), m), c), m), a);
		lemma_eq_ref(mul_(a, d));
	}
	let temp_34_0 = (mul_((mod_((mul_(d, d)), m)), (mul_((mod_(b, m)), d))));
	let temp_34_1 = (mul_((mul_((mod_((mul_(d, d)), m)), (mod_(b, m)))), d));
	assert(eq_(temp_34_0, temp_34_1)) by {
		lemma_mul_assoc(mod_(mul_(d, d), m), mod_(b, m), d);
	}
	let temp_35_0 = (mul_(b, (mul_(c, c))));
	let temp_35_1 = (mul_((mul_(c, c)), b));
	assert(eq_(temp_35_0, temp_35_1)) by {
		lemma_mul_comm(b, mul_(c, c));
	}
	let temp_36_0 = (mul_((mul_(b, d)), (mul_(b, d))));
	let temp_36_1 = (mul_((mul_(b, d)), (mul_(d, b))));
	assert(eq_(temp_36_0, temp_36_1)) by {
		cong_mul_(mul_(b, d), mul_(b, d), mul_(b, d), mul_(d, b));
		lemma_mul_comm(b, d);
		lemma_eq_ref(mul_(b, d));
	}
	let temp_37_0 = (mul_((mod_((mul_(a, c)), m)), (mod_((add_(d, d)), m))));
	let temp_37_1 = (mul_((mod_((mul_(a, c)), m)), (mod_((add_((mod_(d, m)), (mod_(d, m)))), m))));
	assert(eq_(temp_37_0, temp_37_1)) by {
		lemma_mod_add_noop(d, d, m);
		cong_mul_(mod_(mul_(a, c), m), mod_(add_(d, d), m), mod_(mul_(a, c), m), mod_(add_(mod_(d, m), mod_(d, m)), m));
		lemma_eq_ref(mod_(mul_(a, c), m));
	}
	let temp_38_0 = (mul_((mul_(a, d)), c));
	let temp_38_1 = (mul_((mul_(d, a)), c));
	assert(eq_(temp_38_0, temp_38_1)) by {
		lemma_eq_ref(c);
		cong_mul_(mul_(a, d), c, mul_(d, a), c);
		lemma_mul_comm(a, d);
	}
	let temp_39_0 = (mul_((mul_(d, d)), (mul_(d, d))));
	let temp_39_1 = (mul_((mul_(d, d)), (mul_(d, d))));
	assert(eq_(temp_39_0, temp_39_1)) by {
		lemma_eq_ref(temp_39_0);
	}
	let temp_40_0 = (mul_((mul_(c, d)), (mod_((mul_(c, d)), m))));
	let temp_40_1 = (mul_(c, (mul_(d, (mod_((mul_(c, d)), m))))));
	assert(eq_(temp_40_0, temp_40_1)) by {
		lemma_eq_sym(temp_40_1, temp_40_0);
		lemma_mul_assoc(c, d, mod_(mul_(c, d), m));
	}
	let temp_41_0 = (mod_((mul_((mod_((add_(c, d)), m)), (mul_(b, as_elem(100))))), m));
	let temp_41_1 = (mod_((mul_((mod_((add_(d, c)), m)), (mul_(b, as_elem(100))))), m));
	assert(eq_(temp_41_0, temp_41_1)) by {
		lemma_add_comm(c, d);
		cong_mod_(mul_(mod_(add_(c, d), m), mul_(b, as_elem(100))), m, mul_(mod_(add_(d, c), m), mul_(b, as_elem(100))), m);
		lemma_eq_ref(mul_(b, as_elem(100)));
		lemma_eq_ref(m);
		cong_mul_(mod_(add_(c, d), m), mul_(b, as_elem(100)), mod_(add_(d, c), m), mul_(b, as_elem(100)));
		cong_mod_(add_(c, d), m, add_(d, c), m);
	}
	let temp_42_0 = (mul_((mul_(b, (mod_(d, m)))), (mul_(a, d))));
	let temp_42_1 = (mul_((mul_(b, (mod_((add_(d, (mul_((mul_((mul_(d, a)), (mul_(c, a)))), m)))), m)))), (mul_(a, d))));
	assert(eq_(temp_42_0, temp_42_1)) by {
		cong_mul_(b, mod_(d, m), b, mod_(add_(d, mul_(mul_(mul_(d, a), mul_(c, a)), m)), m));
		lemma_eq_ref(b);
		lemma_mod_mul_vanish(d, mul_(mul_(d, a), mul_(c, a)), m);
		cong_mul_(mul_(b, mod_(d, m)), mul_(a, d), mul_(b, mod_(add_(d, mul_(mul_(mul_(d, a), mul_(c, a)), m)), m)), mul_(a, d));
		lemma_eq_ref(mul_(a, d));
	}
	let temp_43_0 = (mul_((mul_((mod_(b, m)), d)), (mul_(b, a))));
	let temp_43_1 = (mul_((mul_((mul_((mod_(b, m)), d)), b)), a));
	assert(eq_(temp_43_0, temp_43_1)) by {
		lemma_mul_assoc(mul_(mod_(b, m), d), b, a);
	}
	let temp_44_0 = (mul_((mul_(c, d)), (mul_(d, d))));
	let temp_44_1 = (mul_((mul_(d, c)), (mul_(d, d))));
	assert(eq_(temp_44_0, temp_44_1)) by {
		cong_mul_(mul_(c, d), mul_(d, d), mul_(d, c), mul_(d, d));
		lemma_mul_comm(c, d);
		lemma_mul_comm(d, d);
	}
	let temp_45_0 = (mul_((mul_(c, as_elem(76))), (add_(d, b))));
	let temp_45_1 = (mul_((add_(d, b)), (mul_(c, as_elem(76)))));
	assert(eq_(temp_45_0, temp_45_1)) by {
		lemma_mul_comm(mul_(c, as_elem(76)), add_(d, b));
	}
	let temp_46_0 = (mul_((mul_(b, b)), (sub_(b, c))));
	let temp_46_1 = (mul_(b, (mul_(b, (sub_(b, c))))));
	assert(eq_(temp_46_0, temp_46_1)) by {
		lemma_eq_sym(temp_46_1, temp_46_0);
		lemma_mul_assoc(b, b, sub_(b, c));
	}
	let temp_47_0 = (sub_((mul_(c, a)), b));
	let temp_47_1 = (sub_((mul_(a, c)), b));
	assert(eq_(temp_47_0, temp_47_1)) by {
		cong_sub_(mul_(c, a), b, mul_(a, c), b);
		lemma_mul_comm(c, a);
		lemma_eq_ref(b);
	}
	let temp_48_0 = (mul_((mul_(b, b)), (add_(b, c))));
	let temp_48_1 = (add_((mul_((mul_(b, b)), b)), (mul_((mul_(b, b)), c))));
	assert(eq_(temp_48_0, temp_48_1)) by {
		lemma_mul_dist(mul_(b, b), b, c);
	}
	let temp_49_0 = (sub_((add_(c, d)), a));
	let temp_49_1 = (sub_((add_(d, c)), a));
	assert(eq_(temp_49_0, temp_49_1)) by {
		cong_sub_(add_(c, d), a, add_(d, c), a);
		lemma_add_comm(c, d);
		lemma_eq_ref(a);
	}
	let temp_50_0 = (mul_((mul_(a, b)), (mul_(c, b))));
	let temp_50_1 = (mul_((mul_(a, b)), (mul_(b, c))));
	assert(eq_(temp_50_0, temp_50_1)) by {
		cong_mul_(mul_(a, b), mul_(c, b), mul_(a, b), mul_(b, c));
		lemma_mul_comm(c, b);
		lemma_eq_ref(mul_(a, b));
	}
	let temp_51_0 = (mul_((mul_(a, c)), c));
	let temp_51_1 = (mul_(c, (mul_(a, c))));
	assert(eq_(temp_51_0, temp_51_1)) by {
		lemma_mul_comm(mul_(a, c), c);
	}
	let temp_52_0 = (mul_((mod_((add_((mod_(d, m)), b)), m)), (mul_(c, (mod_(d, m))))));
	let temp_52_1 = (mul_((mul_((mod_((add_((mod_(d, m)), b)), m)), c)), (mod_(d, m))));
	assert(eq_(temp_52_0, temp_52_1)) by {
		lemma_mul_assoc(mod_(add_(mod_(d, m), b), m), c, mod_(d, m));
	}
	let temp_53_0 = (mod_((mul_((add_(b, c)), (mod_((mul_(c, c)), m)))), m));
	let temp_53_1 = (mod_((mul_((add_(c, b)), (mod_((mul_(c, c)), m)))), m));
	assert(eq_(temp_53_0, temp_53_1)) by {
		lemma_add_comm(b, c);
		cong_mod_(mul_(add_(b, c), mod_(mul_(c, c), m)), m, mul_(add_(c, b), mod_(mul_(c, c), m)), m);
		lemma_eq_ref(mod_(mul_(c, c), m));
		cong_mul_(add_(b, c), mod_(mul_(c, c), m), add_(c, b), mod_(mul_(c, c), m));
		lemma_eq_ref(m);
	}
	let temp_54_0 = (mod_((mul_((mul_(b, a)), (mul_(c, a)))), m));
	let temp_54_1 = (mod_((add_((mul_((mul_(b, a)), (mul_(c, a)))), (mul_((mul_((mul_(d, a)), (mod_((mul_(b, (mod_(a, m)))), m)))), m)))), m));
	assert(eq_(temp_54_0, temp_54_1)) by {
		lemma_mod_mul_vanish(mul_(mul_(b, a), mul_(c, a)), mul_(mul_(d, a), mod_(mul_(b, mod_(a, m)), m)), m);
	}
	let temp_55_0 = (mul_((mul_(c, b)), (mul_(c, b))));
	let temp_55_1 = (mul_((mul_((mul_(c, b)), c)), b));
	assert(eq_(temp_55_0, temp_55_1)) by {
		lemma_mul_assoc(mul_(c, b), c, b);
	}
	let temp_56_0 = (mul_((mul_(b, a)), (sub_(a, a))));
	let temp_56_1 = (mul_((mul_(a, b)), (sub_(a, a))));
	assert(eq_(temp_56_0, temp_56_1)) by {
		cong_mul_(mul_(b, a), sub_(a, a), mul_(a, b), sub_(a, a));
		lemma_mul_comm(b, a);
		lemma_eq_ref(sub_(a, a));
	}
	let temp_57_0 = (mul_((mul_(a, c)), (mul_(b, b))));
	let temp_57_1 = (mul_(a, (mul_(c, (mul_(b, b))))));
	assert(eq_(temp_57_0, temp_57_1)) by {
		lemma_eq_sym(temp_57_1, temp_57_0);
		lemma_mul_assoc(a, c, mul_(b, b));
	}
	let temp_58_0 = (mul_((mul_(b, b)), (add_(a, b))));
	let temp_58_1 = (mul_((mul_(b, b)), (add_(b, a))));
	assert(eq_(temp_58_0, temp_58_1)) by {
		cong_mul_(mul_(b, b), add_(a, b), mul_(b, b), add_(b, a));
		lemma_add_comm(a, b);
		lemma_mul_comm(b, b);
	}
	let temp_59_0 = (mul_((mul_(a, d)), (mul_(d, as_elem(89)))));
	let temp_59_1 = (mul_(a, (mul_(d, (mul_(d, as_elem(89)))))));
	assert(eq_(temp_59_0, temp_59_1)) by {
		lemma_eq_sym(temp_59_1, temp_59_0);
		lemma_mul_assoc(a, d, mul_(d, as_elem(89)));
	}
	let temp_60_0 = (mul_((mod_((add_(b, d)), m)), (sub_(c, c))));
	let temp_60_1 = (mul_((mod_((add_((mod_(b, m)), (mod_(d, m)))), m)), (sub_(c, c))));
	assert(eq_(temp_60_0, temp_60_1)) by {
		lemma_mod_add_noop(b, d, m);
		cong_mul_(mod_(add_(b, d), m), sub_(c, c), mod_(add_(mod_(b, m), mod_(d, m)), m), sub_(c, c));
		lemma_eq_ref(sub_(c, c));
	}
	let temp_61_0 = (add_((mul_(d, a)), (mul_(a, c))));
	let temp_61_1 = (add_((mul_(a, c)), (mul_(d, a))));
	assert(eq_(temp_61_0, temp_61_1)) by {
		lemma_add_comm(mul_(d, a), mul_(a, c));
	}
	let temp_62_0 = (mul_((sub_(as_elem(73), c)), (mul_(a, d))));
	let temp_62_1 = (mul_((mul_(a, d)), (sub_(as_elem(73), c))));
	assert(eq_(temp_62_0, temp_62_1)) by {
		lemma_mul_comm(sub_(as_elem(73), c), mul_(a, d));
	}
	let temp_63_0 = (add_((mod_((mul_((mod_(c, m)), b)), m)), (mul_(as_elem(35), a))));
	let temp_63_1 = (add_((mod_((mul_(b, (mod_(c, m)))), m)), (mul_(as_elem(35), a))));
	assert(eq_(temp_63_0, temp_63_1)) by {
		lemma_mul_comm(mod_(c, m), b);
		cong_add_(mod_(mul_(mod_(c, m), b), m), mul_(as_elem(35), a), mod_(mul_(b, mod_(c, m)), m), mul_(as_elem(35), a));
		lemma_eq_ref(m);
		cong_mod_(mul_(mod_(c, m), b), m, mul_(b, mod_(c, m)), m);
		lemma_eq_ref(mul_(as_elem(35), a));
	}
	let temp_64_0 = (mul_((mul_(c, c)), (mul_((mod_(c, m)), c))));
	let temp_64_1 = (mul_((mul_((mul_(c, c)), (mod_(c, m)))), c));
	assert(eq_(temp_64_0, temp_64_1)) by {
		lemma_mul_assoc(mul_(c, c), mod_(c, m), c);
	}
	let temp_65_0 = (mul_(a, (mul_(a, (mod_(d, m))))));
	let temp_65_1 = (mul_(a, (mul_((mod_(d, m)), a))));
	assert(eq_(temp_65_0, temp_65_1)) by {
		cong_mul_(a, mul_(a, mod_(d, m)), a, mul_(mod_(d, m), a));
		lemma_mul_comm(a, mod_(d, m));
		lemma_eq_ref(a);
	}
	let temp_66_0 = (mul_((sub_(b, d)), (add_(d, a))));
	let temp_66_1 = (mul_((sub_(b, d)), (add_(a, d))));
	assert(eq_(temp_66_0, temp_66_1)) by {
		cong_mul_(sub_(b, d), add_(d, a), sub_(b, d), add_(a, d));
		lemma_add_comm(d, a);
		lemma_eq_ref(sub_(b, d));
	}
	let temp_67_0 = (mod_((mul_((mul_(d, d)), (mul_((mod_(d, m)), b)))), m));
	let temp_67_1 = (mod_((mul_(d, (mul_(d, (mul_((mod_(d, m)), b)))))), m));
	assert(eq_(temp_67_0, temp_67_1)) by {
		lemma_mul_assoc(d, d, mul_(mod_(d, m), b));
		cong_mod_(mul_(mul_(d, d), mul_(mod_(d, m), b)), m, mul_(d, mul_(d, mul_(mod_(d, m), b))), m);
		lemma_eq_sym(mul_(d, mul_(d, mul_(mod_(d, m), b))), mul_(mul_(d, d), mul_(mod_(d, m), b)));
		lemma_eq_ref(m);
	}
	let temp_68_0 = (mul_((mod_(a, m)), (mul_(b, d))));
	let temp_68_1 = (mul_((mod_(a, m)), (mul_(d, b))));
	assert(eq_(temp_68_0, temp_68_1)) by {
		cong_mul_(mod_(a, m), mul_(b, d), mod_(a, m), mul_(d, b));
		lemma_mul_comm(b, d);
		lemma_eq_ref(mod_(a, m));
	}
	let temp_69_0 = (mul_((mod_((mul_(c, b)), m)), (add_(c, c))));
	let temp_69_1 = (mul_((mod_((mul_(c, b)), m)), (add_(c, c))));
	assert(eq_(temp_69_0, temp_69_1)) by {
		lemma_eq_ref(temp_69_0);
	}
	let temp_70_0 = (mul_((mul_(a, a)), (mul_((mod_(a, m)), d))));
	let temp_70_1 = (mul_((mul_(a, a)), (mul_((mod_((add_(a, (mul_((mul_((sub_(d, b)), (mul_(b, d)))), m)))), m)), d))));
	assert(eq_(temp_70_0, temp_70_1)) by {
		lemma_mul_comm(a, a);
		lemma_mod_mul_vanish(a, mul_(sub_(d, b), mul_(b, d)), m);
		cong_mul_(mul_(a, a), mul_(mod_(a, m), d), mul_(a, a), mul_(mod_(add_(a, mul_(mul_(sub_(d, b), mul_(b, d)), m)), m), d));
		lemma_eq_ref(d);
		cong_mul_(mod_(a, m), d, mod_(add_(a, mul_(mul_(sub_(d, b), mul_(b, d)), m)), m), d);
	}
	let temp_71_0 = (mul_((mul_(a, b)), (mul_(d, c))));
	let temp_71_1 = (mul_((mul_((mul_(a, b)), d)), c));
	assert(eq_(temp_71_0, temp_71_1)) by {
		lemma_mul_assoc(mul_(a, b), d, c);
	}
	let temp_72_0 = (mul_((sub_(as_elem(11), a)), (mul_(d, a))));
	let temp_72_1 = (mul_((mul_((sub_(as_elem(11), a)), d)), a));
	assert(eq_(temp_72_0, temp_72_1)) by {
		lemma_mul_assoc(sub_(as_elem(11), a), d, a);
	}
	let temp_73_0 = (mul_((mul_(c, c)), (mul_(c, (mod_(c, m))))));
	let temp_73_1 = (mul_((mul_(c, (mod_(c, m)))), (mul_(c, c))));
	assert(eq_(temp_73_0, temp_73_1)) by {
		lemma_mul_comm(mul_(c, c), mul_(c, mod_(c, m)));
	}
	let temp_74_0 = (mod_((mul_((mul_(c, c)), a)), m));
	let temp_74_1 = (mod_((mul_((mul_(c, c)), a)), m));
	assert(eq_(temp_74_0, temp_74_1)) by {
		lemma_eq_ref(temp_74_0);
	}
	let temp_75_0 = (mul_((mul_(c, d)), (mul_((mod_(a, m)), b))));
	let temp_75_1 = (mul_((mul_((mul_(c, d)), (mod_(a, m)))), b));
	assert(eq_(temp_75_0, temp_75_1)) by {
		lemma_mul_assoc(mul_(c, d), mod_(a, m), b);
	}
	let temp_76_0 = (mul_((mul_(d, d)), (mul_(d, (mod_(b, m))))));
	let temp_76_1 = (mul_((mul_(d, d)), (mul_(d, (mod_((add_((mul_((mul_((mul_(c, a)), (mod_((mul_(a, c)), m)))), m)), b)), m))))));
	assert(eq_(temp_76_0, temp_76_1)) by {
		lemma_mul_comm(d, d);
		lemma_mod_mul_vanish(b, mul_(mul_(c, a), mod_(mul_(a, c), m)), m);
		cong_mul_(mul_(d, d), mul_(d, mod_(b, m)), mul_(d, d), mul_(d, mod_(add_(mul_(mul_(mul_(c, a), mod_(mul_(a, c), m)), m), b), m)));
		lemma_eq_ref(d);
		cong_mul_(d, mod_(b, m), d, mod_(add_(mul_(mul_(mul_(c, a), mod_(mul_(a, c), m)), m), b), m));
	}
	let temp_77_0 = (mul_((mul_(b, b)), b));
	let temp_77_1 = (mul_(b, (mul_(b, b))));
	assert(eq_(temp_77_0, temp_77_1)) by {
		lemma_mul_comm(mul_(b, b), b);
	}
	let temp_78_0 = (mul_((mod_((sub_((mod_(b, m)), b)), m)), (mul_(c, a))));
	let temp_78_1 = (mul_((mul_((mod_((sub_((mod_(b, m)), b)), m)), c)), a));
	assert(eq_(temp_78_0, temp_78_1)) by {
		lemma_mul_assoc(mod_(sub_(mod_(b, m), b), m), c, a);
	}
	let temp_79_0 = (mul_((mod_((mul_(b, d)), m)), (sub_(a, (mod_(b, m))))));
	let temp_79_1 = (mul_((mod_((add_((mul_(b, d)), (mul_((add_((mul_((mod_(d, m)), d)), (mul_(d, a)))), m)))), m)), (sub_(a, (mod_(b, m))))));
	assert(eq_(temp_79_0, temp_79_1)) by {
		lemma_mod_mul_vanish(mul_(b, d), add_(mul_(mod_(d, m), d), mul_(d, a)), m);
		cong_mul_(mod_(mul_(b, d), m), sub_(a, mod_(b, m)), mod_(add_(mul_(b, d), mul_(add_(mul_(mod_(d, m), d), mul_(d, a)), m)), m), sub_(a, mod_(b, m)));
		lemma_eq_ref(sub_(a, mod_(b, m)));
	}
	let temp_80_0 = (mul_((mul_(d, d)), (mod_((mul_(d, d)), m))));
	let temp_80_1 = (mul_(d, (mul_(d, (mod_((mul_(d, d)), m))))));
	assert(eq_(temp_80_0, temp_80_1)) by {
		lemma_eq_sym(temp_80_1, temp_80_0);
		lemma_mul_assoc(d, d, mod_(mul_(d, d), m));
	}
	let temp_81_0 = (mul_((mul_(d, (mod_(c, m)))), (mul_(b, a))));
	let temp_81_1 = (mul_((mul_((mod_(c, m)), d)), (mul_(b, a))));
	assert(eq_(temp_81_0, temp_81_1)) by {
		lemma_mul_comm(d, mod_(c, m));
		cong_mul_(mul_(d, mod_(c, m)), mul_(b, a), mul_(mod_(c, m), d), mul_(b, a));
		lemma_eq_ref(mul_(b, a));
	}
	let temp_82_0 = (mod_((mul_((mod_((mul_((mod_(c, m)), a)), m)), (mul_(d, a)))), m));
	let temp_82_1 = (mod_((mul_((mod_((sub_((mul_((mod_(c, m)), a)), (mul_((mul_((mul_(c, b)), (mul_((mod_(b, m)), c)))), m)))), m)), (mul_(d, a)))), m));
	assert(eq_(temp_82_0, temp_82_1)) by {
		lemma_mod_mul_vanish(mul_(mod_(c, m), a), mul_(mul_(c, b), mul_(mod_(b, m), c)), m);
		cong_mod_(mul_(mod_(mul_(mod_(c, m), a), m), mul_(d, a)), m, mul_(mod_(sub_(mul_(mod_(c, m), a), mul_(mul_(mul_(c, b), mul_(mod_(b, m), c)), m)), m), mul_(d, a)), m);
		cong_mul_(mod_(mul_(mod_(c, m), a), m), mul_(d, a), mod_(sub_(mul_(mod_(c, m), a), mul_(mul_(mul_(c, b), mul_(mod_(b, m), c)), m)), m), mul_(d, a));
		lemma_eq_ref(mul_(d, a));
		lemma_eq_ref(m);
	}
	let temp_83_0 = (mul_((mul_(a, d)), (mul_(d, d))));
	let temp_83_1 = (mul_(a, (mul_(d, (mul_(d, d))))));
	assert(eq_(temp_83_0, temp_83_1)) by {
		lemma_eq_sym(temp_83_1, temp_83_0);
		lemma_mul_assoc(a, d, mul_(d, d));
	}
	let temp_84_0 = (mul_((mul_(d, d)), (mul_(b, b))));
	let temp_84_1 = (mul_((mul_(d, d)), (mul_(b, b))));
	assert(eq_(temp_84_0, temp_84_1)) by {
		lemma_eq_ref(temp_84_0);
	}
	let temp_85_0 = (mul_((mod_((mul_(b, a)), m)), (mul_(a, b))));
	let temp_85_1 = (mul_((mod_((add_((mul_((mul_((mul_(d, c)), (mul_(c, c)))), m)), (mul_(b, a)))), m)), (mul_(a, b))));
	assert(eq_(temp_85_0, temp_85_1)) by {
		lemma_mod_mul_vanish(mul_(b, a), mul_(mul_(d, c), mul_(c, c)), m);
		cong_mul_(mod_(mul_(b, a), m), mul_(a, b), mod_(add_(mul_(mul_(mul_(d, c), mul_(c, c)), m), mul_(b, a)), m), mul_(a, b));
		lemma_eq_ref(mul_(a, b));
	}
	let temp_86_0 = (mul_((mul_(d, b)), (mul_(a, c))));
	let temp_86_1 = (mul_((mul_(b, d)), (mul_(a, c))));
	assert(eq_(temp_86_0, temp_86_1)) by {
		cong_mul_(mul_(d, b), mul_(a, c), mul_(b, d), mul_(a, c));
		lemma_mul_comm(d, b);
		lemma_eq_ref(mul_(a, c));
	}
	let temp_87_0 = (mul_((mul_(a, c)), (mul_(c, d))));
	let temp_87_1 = (mul_((mul_(a, c)), (mul_(d, c))));
	assert(eq_(temp_87_0, temp_87_1)) by {
		cong_mul_(mul_(a, c), mul_(c, d), mul_(a, c), mul_(d, c));
		lemma_mul_comm(c, d);
		lemma_eq_ref(mul_(a, c));
	}
	let temp_88_0 = (mul_(c, (sub_(a, b))));
	let temp_88_1 = (mul_((sub_(a, b)), c));
	assert(eq_(temp_88_0, temp_88_1)) by {
		lemma_mul_comm(c, sub_(a, b));
	}
	let temp_89_0 = (mul_((sub_(b, c)), (mul_(b, c))));
	let temp_89_1 = (mul_((mul_((sub_(b, c)), b)), c));
	assert(eq_(temp_89_0, temp_89_1)) by {
		lemma_mul_assoc(sub_(b, c), b, c);
	}
	let temp_90_0 = (mul_((mul_(a, d)), (mul_(b, d))));
	let temp_90_1 = (mul_((mul_(d, a)), (mul_(b, d))));
	assert(eq_(temp_90_0, temp_90_1)) by {
		cong_mul_(mul_(a, d), mul_(b, d), mul_(d, a), mul_(b, d));
		lemma_mul_comm(a, d);
		lemma_eq_ref(mul_(b, d));
	}
	let temp_91_0 = (mul_((mul_(b, c)), (add_(d, c))));
	let temp_91_1 = (mul_(b, (mul_(c, (add_(d, c))))));
	assert(eq_(temp_91_0, temp_91_1)) by {
		lemma_eq_sym(temp_91_1, temp_91_0);
		lemma_mul_assoc(b, c, add_(d, c));
	}
	let temp_92_0 = (sub_((add_(c, b)), (sub_(b, b))));
	let temp_92_1 = (sub_((add_(b, c)), (sub_(b, b))));
	assert(eq_(temp_92_0, temp_92_1)) by {
		cong_sub_(add_(c, b), sub_(b, b), add_(b, c), sub_(b, b));
		lemma_add_comm(c, b);
		lemma_eq_ref(sub_(b, b));
	}
	let temp_93_0 = (mul_((mod_((mul_(c, d)), m)), (sub_(b, d))));
	let temp_93_1 = (mul_((mod_((add_((mul_((mul_(c, (mul_(c, (mod_(d, m)))))), m)), (mul_(c, d)))), m)), (sub_(b, d))));
	assert(eq_(temp_93_0, temp_93_1)) by {
		lemma_mod_mul_vanish(mul_(c, d), mul_(c, mul_(c, mod_(d, m))), m);
		cong_mul_(mod_(mul_(c, d), m), sub_(b, d), mod_(add_(mul_(mul_(c, mul_(c, mod_(d, m))), m), mul_(c, d)), m), sub_(b, d));
		lemma_eq_ref(sub_(b, d));
	}
	let temp_94_0 = (mul_((mod_((mul_(b, b)), m)), (mul_(b, c))));
	let temp_94_1 = (mul_((mod_((add_((mul_((mul_((mul_(b, c)), (mul_(a, a)))), m)), (mul_(b, b)))), m)), (mul_(b, c))));
	assert(eq_(temp_94_0, temp_94_1)) by {
		lemma_mod_mul_vanish(mul_(b, b), mul_(mul_(b, c), mul_(a, a)), m);
		cong_mul_(mod_(mul_(b, b), m), mul_(b, c), mod_(add_(mul_(mul_(mul_(b, c), mul_(a, a)), m), mul_(b, b)), m), mul_(b, c));
		lemma_eq_ref(mul_(b, c));
	}
	let temp_95_0 = (mul_((mod_((mul_(b, a)), m)), (add_(b, c))));
	let temp_95_1 = (mul_((mod_((mul_(b, a)), m)), (add_(c, b))));
	assert(eq_(temp_95_0, temp_95_1)) by {
		lemma_add_comm(b, c);
		cong_mul_(mod_(mul_(b, a), m), add_(b, c), mod_(mul_(b, a), m), add_(c, b));
		lemma_eq_ref(mod_(mul_(b, a), m));
	}
	let temp_96_0 = (mod_((mul_((mul_(d, a)), (mul_(a, a)))), m));
	let temp_96_1 = (mod_((mul_((mul_(a, a)), (mul_(d, a)))), m));
	assert(eq_(temp_96_0, temp_96_1)) by {
		cong_mod_(mul_(mul_(d, a), mul_(a, a)), m, mul_(mul_(a, a), mul_(d, a)), m);
		lemma_mul_comm(mul_(d, a), mul_(a, a));
		lemma_eq_ref(m);
	}
	let temp_97_0 = (mul_((sub_((mod_(d, m)), (mod_(d, m)))), (add_((mod_(b, m)), d))));
	let temp_97_1 = (mul_((sub_((mod_(d, m)), (mod_(d, m)))), (add_(d, (mod_(b, m))))));
	assert(eq_(temp_97_0, temp_97_1)) by {
		lemma_add_comm(mod_(b, m), d);
		cong_mul_(sub_(mod_(d, m), mod_(d, m)), add_(mod_(b, m), d), sub_(mod_(d, m), mod_(d, m)), add_(d, mod_(b, m)));
		lemma_eq_ref(sub_(mod_(d, m), mod_(d, m)));
	}
	let temp_98_0 = (mul_((mul_(c, d)), (mul_(c, d))));
	let temp_98_1 = (mul_((mul_((mul_(c, d)), c)), d));
	assert(eq_(temp_98_0, temp_98_1)) by {
		lemma_mul_assoc(mul_(c, d), c, d);
	}
	let temp_99_0 = (mul_((mod_((mul_((mod_(a, m)), d)), m)), (mod_((sub_(b, a)), m))));
	let temp_99_1 = (mul_((mod_((mul_((mod_(a, m)), d)), m)), (mod_((sub_(b, (mod_(a, m)))), m))));
	assert(eq_(temp_99_0, temp_99_1)) by {
		cong_mul_(mod_(mul_(mod_(a, m), d), m), mod_(sub_(b, a), m), mod_(mul_(mod_(a, m), d), m), mod_(sub_(b, mod_(a, m)), m));
		lemma_mod_sub_noop(b, a, m);
		lemma_eq_ref(mod_(mul_(mod_(a, m), d), m));
	}
	let temp_100_0 = (mul_((mul_(d, c)), (mul_(b, c))));
	let temp_100_1 = (mul_((mul_(d, c)), (mul_(c, b))));
	assert(eq_(temp_100_0, temp_100_1)) by {
		cong_mul_(mul_(d, c), mul_(b, c), mul_(d, c), mul_(c, b));
		lemma_mul_comm(b, c);
		lemma_eq_ref(mul_(d, c));
	}
	let temp_101_0 = (add_((mul_(a, (mod_(d, m)))), (mul_(c, c))));
	let temp_101_1 = (add_((mul_(a, (mod_((add_(d, (mul_((mul_((mul_(d, a)), (mul_(d, b)))), m)))), m)))), (mul_(c, c))));
	assert(eq_(temp_101_0, temp_101_1)) by {
		lemma_mod_mul_vanish(d, mul_(mul_(d, a), mul_(d, b)), m);
		cong_add_(mul_(a, mod_(d, m)), mul_(c, c), mul_(a, mod_(add_(d, mul_(mul_(mul_(d, a), mul_(d, b)), m)), m)), mul_(c, c));
		lemma_eq_ref(a);
		lemma_eq_ref(mul_(c, c));
		cong_mul_(a, mod_(d, m), a, mod_(add_(d, mul_(mul_(mul_(d, a), mul_(d, b)), m)), m));
	}
	let temp_102_0 = (mul_((mul_(a, (mod_(d, m)))), (mul_(b, d))));
	let temp_102_1 = (mul_((mul_(a, (mod_(d, m)))), (mul_(d, b))));
	assert(eq_(temp_102_0, temp_102_1)) by {
		lemma_mul_comm(b, d);
		cong_mul_(mul_(a, mod_(d, m)), mul_(b, d), mul_(a, mod_(d, m)), mul_(d, b));
		lemma_eq_ref(mul_(a, mod_(d, m)));
	}
	let temp_103_0 = (mul_((add_(b, b)), (mul_(d, c))));
	let temp_103_1 = (add_((mul_(b, (mul_(d, c)))), (mul_(b, (mul_(d, c))))));
	assert(eq_(temp_103_0, temp_103_1)) by {
		lemma_mul_dist(b, b, mul_(d, c));
	}
	let temp_104_0 = (add_((mul_(b, d)), (add_(c, d))));
	let temp_104_1 = (add_((mul_(d, b)), (add_(c, d))));
	assert(eq_(temp_104_0, temp_104_1)) by {
		cong_add_(mul_(b, d), add_(c, d), mul_(d, b), add_(c, d));
		lemma_mul_comm(b, d);
		lemma_eq_ref(add_(c, d));
	}
	let temp_105_0 = (mul_((mul_(c, a)), (mul_(a, c))));
	let temp_105_1 = (mul_((mul_(a, c)), (mul_(a, c))));
	assert(eq_(temp_105_0, temp_105_1)) by {
		cong_mul_(mul_(c, a), mul_(a, c), mul_(a, c), mul_(a, c));
		lemma_mul_comm(c, a);
		lemma_eq_ref(mul_(a, c));
	}
	let temp_106_0 = (mul_((mul_(a, c)), (mul_(c, c))));
	let temp_106_1 = (mul_((mul_(c, c)), (mul_(a, c))));
	assert(eq_(temp_106_0, temp_106_1)) by {
		lemma_mul_comm(mul_(a, c), mul_(c, c));
	}
	let temp_107_0 = (mul_((mul_(b, c)), (mul_(d, a))));
	let temp_107_1 = (mul_((mul_(d, a)), (mul_(b, c))));
	assert(eq_(temp_107_0, temp_107_1)) by {
		lemma_mul_comm(mul_(b, c), mul_(d, a));
	}
	let temp_108_0 = (mul_((mul_((mod_(d, m)), d)), (mod_((mul_(b, b)), m))));
	let temp_108_1 = (mul_((mul_((mod_((add_(d, (mul_((mul_((mul_((mod_(b, m)), d)), (mul_(b, c)))), m)))), m)), d)), (mod_((mul_(b, b)), m))));
	assert(eq_(temp_108_0, temp_108_1)) by {
		cong_mul_(mod_(d, m), d, mod_(add_(d, mul_(mul_(mul_(mod_(b, m), d), mul_(b, c)), m)), m), d);
		lemma_eq_ref(mod_(mul_(b, b), m));
		lemma_eq_ref(d);
		lemma_mod_mul_vanish(d, mul_(mul_(mod_(b, m), d), mul_(b, c)), m);
		cong_mul_(mul_(mod_(d, m), d), mod_(mul_(b, b), m), mul_(mod_(add_(d, mul_(mul_(mul_(mod_(b, m), d), mul_(b, c)), m)), m), d), mod_(mul_(b, b), m));
	}
	let temp_109_0 = (mul_((mod_(a, m)), (mul_((mod_(b, m)), b))));
	let temp_109_1 = (mul_((mul_((mod_(b, m)), b)), (mod_(a, m))));
	assert(eq_(temp_109_0, temp_109_1)) by {
		lemma_mul_comm(mod_(a, m), mul_(mod_(b, m), b));
	}
	let temp_110_0 = (sub_((mul_(d, as_elem(100))), (mul_(d, (mod_(a, m))))));
	let temp_110_1 = (sub_((mul_(as_elem(100), d)), (mul_(d, (mod_(a, m))))));
	assert(eq_(temp_110_0, temp_110_1)) by {
		lemma_mul_comm(d, as_elem(100));
		cong_sub_(mul_(d, as_elem(100)), mul_(d, mod_(a, m)), mul_(as_elem(100), d), mul_(d, mod_(a, m)));
		lemma_eq_ref(mul_(d, mod_(a, m)));
	}
	let temp_111_0 = (mul_((mul_(d, b)), (mul_(a, d))));
	let temp_111_1 = (mul_((mul_(b, d)), (mul_(a, d))));
	assert(eq_(temp_111_0, temp_111_1)) by {
		cong_mul_(mul_(d, b), mul_(a, d), mul_(b, d), mul_(a, d));
		lemma_mul_comm(d, b);
		lemma_eq_ref(mul_(a, d));
	}
	let temp_112_0 = (mul_((mul_(b, d)), (mul_(a, a))));
	let temp_112_1 = (mul_((mul_(d, b)), (mul_(a, a))));
	assert(eq_(temp_112_0, temp_112_1)) by {
		cong_mul_(mul_(b, d), mul_(a, a), mul_(d, b), mul_(a, a));
		lemma_mul_comm(b, d);
		lemma_mul_comm(a, a);
	}
	let temp_113_0 = (mul_((add_(d, b)), (add_(c, b))));
	let temp_113_1 = (mul_((add_(c, b)), (add_(d, b))));
	assert(eq_(temp_113_0, temp_113_1)) by {
		lemma_mul_comm(add_(d, b), add_(c, b));
	}
	let temp_114_0 = (mul_((mul_((mod_(a, m)), b)), (mul_(c, d))));
	let temp_114_1 = (mul_((mul_((mod_((add_((mul_((mul_((mul_(d, a)), (mul_((mod_(a, m)), c)))), m)), a)), m)), b)), (mul_(c, d))));
	assert(eq_(temp_114_0, temp_114_1)) by {
		lemma_mul_comm(d, c);
		lemma_mul_comm(c, d);
		lemma_mod_mul_vanish(a, mul_(mul_(d, a), mul_(mod_(a, m), c)), m);
		cong_mul_(mul_(mod_(a, m), b), mul_(c, d), mul_(mod_(add_(mul_(mul_(mul_(d, a), mul_(mod_(a, m), c)), m), a), m), b), mul_(c, d));
		lemma_eq_trans(mul_(c, d), mul_(d, c), mul_(c, d));
		lemma_eq_ref(b);
		cong_mul_(mod_(a, m), b, mod_(add_(mul_(mul_(mul_(d, a), mul_(mod_(a, m), c)), m), a), m), b);
	}
	let temp_115_0 = (mul_((mul_(b, d)), (mod_((sub_(d, d)), m))));
	let temp_115_1 = (mul_((mod_((sub_(d, d)), m)), (mul_(b, d))));
	assert(eq_(temp_115_0, temp_115_1)) by {
		lemma_mul_comm(mul_(b, d), mod_(sub_(d, d), m));
	}
	let temp_116_0 = (mul_((mul_(c, a)), (add_(b, d))));
	let temp_116_1 = (add_((mul_((mul_(c, a)), b)), (mul_((mul_(c, a)), d))));
	assert(eq_(temp_116_0, temp_116_1)) by {
		lemma_mul_dist(mul_(c, a), b, d);
	}
	let temp_117_0 = (add_((mul_(c, (mod_(c, m)))), (mod_((mul_((mod_(d, m)), c)), m))));
	let temp_117_1 = (add_((mul_(c, (mod_(c, m)))), (mod_((mul_((mod_((add_(d, (mul_((mul_((mul_(d, d)), (mul_(c, b)))), m)))), m)), c)), m))));
	assert(eq_(temp_117_0, temp_117_1)) by {
		lemma_mod_mul_vanish(d, mul_(mul_(d, d), mul_(c, b)), m);
		cong_add_(mul_(c, mod_(c, m)), mod_(mul_(mod_(d, m), c), m), mul_(c, mod_(c, m)), mod_(mul_(mod_(add_(d, mul_(mul_(mul_(d, d), mul_(c, b)), m)), m), c), m));
		cong_mod_(mul_(mod_(d, m), c), m, mul_(mod_(add_(d, mul_(mul_(mul_(d, d), mul_(c, b)), m)), m), c), m);
		lemma_eq_ref(mul_(c, mod_(c, m)));
		lemma_eq_ref(c);
		cong_mul_(mod_(d, m), c, mod_(add_(d, mul_(mul_(mul_(d, d), mul_(c, b)), m)), m), c);
		lemma_eq_ref(m);
	}
	let temp_118_0 = (mul_((mod_((mul_(a, b)), m)), (mul_(b, b))));
	let temp_118_1 = (mul_((mod_((add_((mul_((mul_((mul_(c, a)), (mul_(d, b)))), m)), (mul_(a, b)))), m)), (mul_(b, b))));
	assert(eq_(temp_118_0, temp_118_1)) by {
		lemma_mul_comm(b, b);
		lemma_mod_mul_vanish(mul_(a, b), mul_(mul_(c, a), mul_(d, b)), m);
		cong_mul_(mod_(mul_(a, b), m), mul_(b, b), mod_(add_(mul_(mul_(mul_(c, a), mul_(d, b)), m), mul_(a, b)), m), mul_(b, b));
	}
	let temp_119_0 = (mul_((mul_(c, d)), (mul_(a, d))));
	let temp_119_1 = (mul_(c, (mul_(d, (mul_(a, d))))));
	assert(eq_(temp_119_0, temp_119_1)) by {
		lemma_eq_sym(temp_119_1, temp_119_0);
		lemma_mul_assoc(c, d, mul_(a, d));
	}
	let temp_120_0 = (mul_((sub_(b, (mod_(b, m)))), (mul_(a, d))));
	let temp_120_1 = (mul_((sub_(b, (mod_((add_((mul_((mul_((mul_(b, c)), (mul_((mod_(b, m)), c)))), m)), b)), m)))), (mul_(a, d))));
	assert(eq_(temp_120_0, temp_120_1)) by {
		lemma_mod_mul_vanish(b, mul_(mul_(b, c), mul_(mod_(b, m), c)), m);
		cong_mul_(sub_(b, mod_(b, m)), mul_(a, d), sub_(b, mod_(add_(mul_(mul_(mul_(b, c), mul_(mod_(b, m), c)), m), b), m)), mul_(a, d));
		cong_sub_(b, mod_(b, m), b, mod_(add_(mul_(mul_(mul_(b, c), mul_(mod_(b, m), c)), m), b), m));
		lemma_eq_ref(mul_(a, d));
		lemma_eq_ref(b);
	}

}

} // verus!