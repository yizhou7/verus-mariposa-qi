use builtin_macros::*;
// use builtin::*;
mod nl_basics;
use crate::nl_basics::*;
verus! {

pub proof fn free_0(a: Elem, b: Elem, c: Elem, d: Elem, m: Elem)
{
	let temp_0_0 = (mul_((mul_(c, d)), (mul_(a, c))));
	let temp_0_1 = (mul_((mul_(a, c)), (mul_(c, d))));
	assert(eq_(temp_0_0, temp_0_1)) by {
		lemma_mul_comm(mul_(c, d), mul_(a, c));
	}
	let temp_1_0 = (mul_((mul_(d, d)), (mul_(d, b))));
	let temp_1_1 = (mul_((mul_((mul_(d, d)), d)), b));
	assert(eq_(temp_1_0, temp_1_1)) by {
		lemma_mul_assoc(mul_(d, d), d, b);
	}
	let temp_2_0 = (mul_((mul_(c, d)), (mul_(b, c))));
	let temp_2_1 = (mul_((mul_(d, c)), (mul_(b, c))));
	assert(eq_(temp_2_0, temp_2_1)) by {
		cong_mul_(mul_(c, d), mul_(b, c), mul_(d, c), mul_(b, c));
		lemma_mul_comm(c, d);
		lemma_eq_ref(mul_(b, c));
	}
	let temp_3_0 = (mul_((mul_(a, as_elem(76))), (mul_(c, c))));
	let temp_3_1 = (mul_((mul_(a, as_elem(76))), (mul_(c, c))));
	assert(eq_(temp_3_0, temp_3_1)) by {
		lemma_eq_ref(temp_3_0);
	}
	let temp_4_0 = (mul_((mul_(d, d)), (sub_(a, c))));
	let temp_4_1 = (mul_((mul_(d, d)), (sub_(a, c))));
	assert(eq_(temp_4_0, temp_4_1)) by {
		lemma_eq_ref(temp_4_0);
	}
	let temp_5_0 = (mul_(c, (mul_(b, c))));
	let temp_5_1 = (mul_((mul_(c, b)), c));
	assert(eq_(temp_5_0, temp_5_1)) by {
		lemma_mul_assoc(c, b, c);
	}
	let temp_6_0 = (mul_((mul_(a, (mod_(a, m)))), (mul_(c, b))));
	let temp_6_1 = (mul_((mul_((mod_(a, m)), a)), (mul_(c, b))));
	assert(eq_(temp_6_0, temp_6_1)) by {
		lemma_mul_comm(a, mod_(a, m));
		cong_mul_(mul_(a, mod_(a, m)), mul_(c, b), mul_(mod_(a, m), a), mul_(c, b));
		lemma_eq_ref(mul_(c, b));
	}
	let temp_7_0 = (mul_((mul_(d, c)), (sub_(a, d))));
	let temp_7_1 = (mul_((mul_(c, d)), (sub_(a, d))));
	assert(eq_(temp_7_0, temp_7_1)) by {
		lemma_eq_ref(sub_(a, d));
		cong_mul_(mul_(d, c), sub_(a, d), mul_(c, d), sub_(a, d));
		lemma_mul_comm(d, c);
	}
	let temp_8_0 = (mul_((add_(c, d)), (mul_(c, a))));
	let temp_8_1 = (mul_((mul_(c, a)), (add_(c, d))));
	assert(eq_(temp_8_0, temp_8_1)) by {
		lemma_mul_comm(add_(c, d), mul_(c, a));
	}
	let temp_9_0 = (mul_((mul_(c, b)), (mul_(d, c))));
	let temp_9_1 = (mul_((mul_((mul_(c, b)), d)), c));
	assert(eq_(temp_9_0, temp_9_1)) by {
		lemma_mul_assoc(mul_(c, b), d, c);
	}
	let temp_10_0 = (mod_((mul_((mul_(d, as_elem(78))), (mul_((mod_(a, m)), d)))), m));
	let temp_10_1 = (mod_((mul_((mul_(as_elem(78), d)), (mul_((mod_(a, m)), d)))), m));
	assert(eq_(temp_10_0, temp_10_1)) by {
		lemma_mul_comm(d, as_elem(78));
		cong_mod_(mul_(mul_(d, as_elem(78)), mul_(mod_(a, m), d)), m, mul_(mul_(as_elem(78), d), mul_(mod_(a, m), d)), m);
		lemma_eq_ref(m);
		lemma_eq_ref(mul_(mod_(a, m), d));
		cong_mul_(mul_(d, as_elem(78)), mul_(mod_(a, m), d), mul_(as_elem(78), d), mul_(mod_(a, m), d));
	}
	let temp_11_0 = (add_((mod_((mul_(b, (mod_(c, m)))), m)), (mod_((mul_(d, a)), m))));
	let temp_11_1 = (add_((mod_((mod_((mul_(b, c)), m)), m)), (mod_((mul_(d, a)), m))));
	assert(eq_(temp_11_0, temp_11_1)) by {
		lemma_mod_mul_noop(b, c, m);
		cong_add_(mod_(mul_(b, mod_(c, m)), m), mod_(mul_(d, a), m), mod_(mod_(mul_(b, c), m), m), mod_(mul_(d, a), m));
		lemma_eq_sym(mod_(mod_(mul_(b, c), m), m), mod_(mul_(b, mod_(c, m)), m));
		lemma_eq_ref(mod_(mul_(d, a), m));
	}
	let temp_12_0 = (mod_((mul_((mul_(b, (mod_(b, m)))), (mod_((mul_(a, a)), m)))), m));
	let temp_12_1 = (mod_((mul_(b, (mul_((mod_(b, m)), (mod_((mul_(a, a)), m)))))), m));
	assert(eq_(temp_12_0, temp_12_1)) by {
		lemma_mul_assoc(b, mod_(b, m), mod_(mul_(a, a), m));
		cong_mod_(mul_(mul_(b, mod_(b, m)), mod_(mul_(a, a), m)), m, mul_(b, mul_(mod_(b, m), mod_(mul_(a, a), m))), m);
		lemma_eq_ref(m);
		lemma_eq_sym(mul_(b, mul_(mod_(b, m), mod_(mul_(a, a), m))), mul_(mul_(b, mod_(b, m)), mod_(mul_(a, a), m)));
	}
	let temp_13_0 = (mul_((mul_(as_elem(39), (mod_(d, m)))), (mul_(d, c))));
	let temp_13_1 = (mul_((mul_((mod_(d, m)), as_elem(39))), (mul_(d, c))));
	assert(eq_(temp_13_0, temp_13_1)) by {
		lemma_mul_comm(as_elem(39), mod_(d, m));
		cong_mul_(mul_(as_elem(39), mod_(d, m)), mul_(d, c), mul_(mod_(d, m), as_elem(39)), mul_(d, c));
		lemma_eq_ref(mul_(d, c));
	}
	let temp_14_0 = (mul_((mul_((mod_(d, m)), d)), (mod_((mul_(d, (mod_(d, m)))), m))));
	let temp_14_1 = (mul_((mul_((mod_((add_((mul_((mul_((mul_(d, a)), (mod_((mul_(a, d)), m)))), m)), d)), m)), d)), (mod_((mul_(d, (mod_(d, m)))), m))));
	assert(eq_(temp_14_0, temp_14_1)) by {
		lemma_mod_mul_vanish(d, mul_(mul_(d, a), mod_(mul_(a, d), m)), m);
		cong_mul_(mul_(mod_(d, m), d), mod_(mul_(d, mod_(d, m)), m), mul_(mod_(add_(mul_(mul_(mul_(d, a), mod_(mul_(a, d), m)), m), d), m), d), mod_(mul_(d, mod_(d, m)), m));
		lemma_eq_ref(d);
		cong_mul_(mod_(d, m), d, mod_(add_(mul_(mul_(mul_(d, a), mod_(mul_(a, d), m)), m), d), m), d);
		lemma_eq_ref(mod_(mul_(d, mod_(d, m)), m));
	}
	let temp_15_0 = (mul_((mul_((mod_(c, m)), c)), (mul_(c, c))));
	let temp_15_1 = (mul_((mul_((mul_((mod_(c, m)), c)), c)), c));
	assert(eq_(temp_15_0, temp_15_1)) by {
		lemma_mul_assoc(mul_(mod_(c, m), c), c, c);
	}
	let temp_16_0 = (add_((mul_((mod_(a, m)), d)), (add_((mod_(d, m)), b))));
	let temp_16_1 = (add_((mul_((mod_(a, m)), d)), (add_(b, (mod_(d, m))))));
	assert(eq_(temp_16_0, temp_16_1)) by {
		lemma_add_comm(mod_(d, m), b);
		cong_add_(mul_(mod_(a, m), d), add_(mod_(d, m), b), mul_(mod_(a, m), d), add_(b, mod_(d, m)));
		lemma_eq_ref(mul_(mod_(a, m), d));
	}
	let temp_17_0 = (mul_((mul_(c, c)), (sub_(c, b))));
	let temp_17_1 = (mul_(c, (mul_(c, (sub_(c, b))))));
	assert(eq_(temp_17_0, temp_17_1)) by {
		lemma_eq_sym(temp_17_1, temp_17_0);
		lemma_mul_assoc(c, c, sub_(c, b));
	}
	let temp_18_0 = (mul_(b, (mul_(a, a))));
	let temp_18_1 = (mul_((mul_(a, a)), b));
	assert(eq_(temp_18_0, temp_18_1)) by {
		lemma_mul_comm(b, mul_(a, a));
	}
	let temp_19_0 = (mul_((mul_(c, d)), (mod_((mul_(c, d)), m))));
	let temp_19_1 = (mul_((mul_(c, d)), (mod_((add_((mul_(c, d)), (mul_((mul_((mul_(c, d)), (mul_(b, c)))), m)))), m))));
	assert(eq_(temp_19_0, temp_19_1)) by {
		lemma_mod_mul_vanish(mul_(c, d), mul_(mul_(c, d), mul_(b, c)), m);
		cong_mul_(mul_(c, d), mod_(mul_(c, d), m), mul_(c, d), mod_(add_(mul_(c, d), mul_(mul_(mul_(c, d), mul_(b, c)), m)), m));
		lemma_eq_ref(mul_(c, d));
	}
	let temp_20_0 = (mul_((mod_((mul_(a, (mod_(c, m)))), m)), (mul_(c, c))));
	let temp_20_1 = (mul_((mod_((mul_(a, (mod_((add_((mul_((mul_((mul_(a, d)), (sub_(c, c)))), m)), c)), m)))), m)), (mul_(c, c))));
	assert(eq_(temp_20_0, temp_20_1)) by {
		lemma_mul_comm(c, c);
		lemma_mod_mul_vanish(c, mul_(mul_(a, d), sub_(c, c)), m);
		cong_mul_(mod_(mul_(a, mod_(c, m)), m), mul_(c, c), mod_(mul_(a, mod_(add_(mul_(mul_(mul_(a, d), sub_(c, c)), m), c), m)), m), mul_(c, c));
		cong_mod_(mul_(a, mod_(c, m)), m, mul_(a, mod_(add_(mul_(mul_(mul_(a, d), sub_(c, c)), m), c), m)), m);
		lemma_eq_ref(a);
		cong_mul_(a, mod_(c, m), a, mod_(add_(mul_(mul_(mul_(a, d), sub_(c, c)), m), c), m));
		lemma_eq_ref(m);
	}
	let temp_21_0 = (mul_((mul_(c, d)), (mul_(b, d))));
	let temp_21_1 = (mul_((mul_((mul_(c, d)), b)), d));
	assert(eq_(temp_21_0, temp_21_1)) by {
		lemma_mul_assoc(mul_(c, d), b, d);
	}
	let temp_22_0 = (mul_((mul_(c, c)), (mul_(b, b))));
	let temp_22_1 = (mul_(c, (mul_(c, (mul_(b, b))))));
	assert(eq_(temp_22_0, temp_22_1)) by {
		lemma_eq_sym(temp_22_1, temp_22_0);
		lemma_mul_assoc(c, c, mul_(b, b));
	}
	let temp_23_0 = (mul_((sub_(d, b)), (sub_(b, c))));
	let temp_23_1 = (sub_((mul_(d, (sub_(b, c)))), (mul_(b, (sub_(b, c))))));
	assert(eq_(temp_23_0, temp_23_1)) by {
		lemma_mul_dist(sub_(b, c), d, b);
	}
	let temp_24_0 = (mul_((mod_((mul_(d, d)), m)), (mod_((mul_(c, b)), m))));
	let temp_24_1 = (mul_((mod_((add_((mul_(d, d)), (mul_((mul_((mod_((mul_(a, (mod_(c, m)))), m)), (mul_(c, c)))), m)))), m)), (mod_((mul_(c, b)), m))));
	assert(eq_(temp_24_0, temp_24_1)) by {
		lemma_mod_mul_vanish(mul_(d, d), mul_(mod_(mul_(a, mod_(c, m)), m), mul_(c, c)), m);
		cong_mul_(mod_(mul_(d, d), m), mod_(mul_(c, b), m), mod_(add_(mul_(d, d), mul_(mul_(mod_(mul_(a, mod_(c, m)), m), mul_(c, c)), m)), m), mod_(mul_(c, b), m));
		lemma_eq_ref(mod_(mul_(c, b), m));
	}
	let temp_25_0 = (mul_((mul_(a, b)), (mul_(c, c))));
	let temp_25_1 = (mul_(a, (mul_(b, (mul_(c, c))))));
	assert(eq_(temp_25_0, temp_25_1)) by {
		lemma_eq_sym(temp_25_1, temp_25_0);
		lemma_mul_assoc(a, b, mul_(c, c));
	}
	let temp_26_0 = (mul_((mul_(b, d)), (add_(b, d))));
	let temp_26_1 = (mul_(b, (mul_(d, (add_(b, d))))));
	assert(eq_(temp_26_0, temp_26_1)) by {
		lemma_eq_sym(temp_26_1, temp_26_0);
		lemma_mul_assoc(b, d, add_(b, d));
	}
	let temp_27_0 = (mul_((mul_(c, a)), (add_(c, a))));
	let temp_27_1 = (mul_((mul_(c, a)), (add_(a, c))));
	assert(eq_(temp_27_0, temp_27_1)) by {
		cong_mul_(mul_(c, a), add_(c, a), mul_(c, a), add_(a, c));
		lemma_add_comm(c, a);
		lemma_eq_ref(mul_(c, a));
	}
	let temp_28_0 = (mul_((mul_(d, d)), (mul_((mod_(b, m)), d))));
	let temp_28_1 = (mul_((mul_((mod_(b, m)), d)), (mul_(d, d))));
	assert(eq_(temp_28_0, temp_28_1)) by {
		lemma_mul_comm(mul_(d, d), mul_(mod_(b, m), d));
	}
	let temp_29_0 = (mul_((mul_(c, b)), (mul_(c, b))));
	let temp_29_1 = (mul_((mul_(c, b)), (mul_(c, b))));
	assert(eq_(temp_29_0, temp_29_1)) by {
		lemma_eq_ref(temp_29_0);
	}
	let temp_30_0 = (mul_((mul_(a, b)), (mul_((mod_(b, m)), c))));
	let temp_30_1 = (mul_((mul_(a, b)), (mul_((mod_((sub_(b, (mul_((mul_((add_(d, c)), (mul_((mod_(a, m)), (mod_(c, m)))))), m)))), m)), c))));
	assert(eq_(temp_30_0, temp_30_1)) by {
		cong_mul_(mul_(a, b), mul_(mod_(b, m), c), mul_(a, b), mul_(mod_(sub_(b, mul_(mul_(add_(d, c), mul_(mod_(a, m), mod_(c, m))), m)), m), c));
		lemma_mod_mul_vanish(b, mul_(add_(d, c), mul_(mod_(a, m), mod_(c, m))), m);
		lemma_eq_ref(c);
		lemma_eq_ref(mul_(a, b));
		cong_mul_(mod_(b, m), c, mod_(sub_(b, mul_(mul_(add_(d, c), mul_(mod_(a, m), mod_(c, m))), m)), m), c);
	}
	let temp_31_0 = (mod_((mul_((add_(c, a)), d)), m));
	let temp_31_1 = (mod_((add_((mul_(c, d)), (mul_(a, d)))), m));
	assert(eq_(temp_31_0, temp_31_1)) by {
		lemma_mul_dist(c, a, d);
		cong_mod_(mul_(add_(c, a), d), m, add_(mul_(c, d), mul_(a, d)), m);
		lemma_eq_ref(m);
	}
	let temp_32_0 = (mul_((mul_(a, d)), (mul_(a, a))));
	let temp_32_1 = (mul_((mul_(a, a)), (mul_(a, d))));
	assert(eq_(temp_32_0, temp_32_1)) by {
		lemma_mul_comm(mul_(a, d), mul_(a, a));
	}
	let temp_33_0 = (mul_((add_(b, d)), (mul_(d, d))));
	let temp_33_1 = (mul_((add_(d, b)), (mul_(d, d))));
	assert(eq_(temp_33_0, temp_33_1)) by {
		cong_mul_(add_(b, d), mul_(d, d), add_(d, b), mul_(d, d));
		lemma_add_comm(b, d);
		lemma_mul_comm(d, d);
	}
	let temp_34_0 = (mul_((mul_((mod_(d, m)), d)), (mul_(c, d))));
	let temp_34_1 = (mul_((mul_((mul_((mod_(d, m)), d)), c)), d));
	assert(eq_(temp_34_0, temp_34_1)) by {
		lemma_mul_assoc(mul_(mod_(d, m), d), c, d);
	}
	let temp_35_0 = (sub_((sub_(d, b)), (mul_(d, b))));
	let temp_35_1 = (sub_((sub_(d, b)), (mul_(b, d))));
	assert(eq_(temp_35_0, temp_35_1)) by {
		cong_sub_(sub_(d, b), mul_(d, b), sub_(d, b), mul_(b, d));
		lemma_mul_comm(d, b);
		lemma_eq_ref(sub_(d, b));
	}
	let temp_36_0 = (add_((mul_(d, d)), (mul_(as_elem(13), a))));
	let temp_36_1 = (add_((mul_(d, d)), (mul_(a, as_elem(13)))));
	assert(eq_(temp_36_0, temp_36_1)) by {
		cong_add_(mul_(d, d), mul_(as_elem(13), a), mul_(d, d), mul_(a, as_elem(13)));
		lemma_mul_comm(as_elem(13), a);
		lemma_eq_ref(mul_(d, d));
	}
	let temp_37_0 = (mul_((mul_(d, (mod_(c, m)))), (mul_(c, a))));
	let temp_37_1 = (mul_((mul_(c, a)), (mul_(d, (mod_(c, m))))));
	assert(eq_(temp_37_0, temp_37_1)) by {
		lemma_mul_comm(mul_(d, mod_(c, m)), mul_(c, a));
	}
	let temp_38_0 = (mul_((mul_(c, a)), (mul_(a, as_elem(5)))));
	let temp_38_1 = (mul_((mul_(a, as_elem(5))), (mul_(c, a))));
	assert(eq_(temp_38_0, temp_38_1)) by {
		lemma_mul_comm(mul_(c, a), mul_(a, as_elem(5)));
	}
	let temp_39_0 = (mul_((mul_(d, a)), (mul_(d, d))));
	let temp_39_1 = (mul_((mul_(d, d)), (mul_(d, a))));
	assert(eq_(temp_39_0, temp_39_1)) by {
		lemma_mul_comm(mul_(d, a), mul_(d, d));
	}
	let temp_40_0 = (mul_((mod_((sub_(d, c)), m)), (mul_(b, a))));
	let temp_40_1 = (mul_((mod_((sub_(d, (mod_(c, m)))), m)), (mul_(b, a))));
	assert(eq_(temp_40_0, temp_40_1)) by {
		cong_mul_(mod_(sub_(d, c), m), mul_(b, a), mod_(sub_(d, mod_(c, m)), m), mul_(b, a));
		lemma_mod_sub_noop(d, c, m);
		lemma_eq_ref(mul_(b, a));
	}
	let temp_41_0 = (mod_((mul_((sub_(d, b)), (mul_(a, d)))), m));
	let temp_41_1 = (mod_((mul_((mul_(a, d)), (sub_(d, b)))), m));
	assert(eq_(temp_41_0, temp_41_1)) by {
		lemma_mul_comm(sub_(d, b), mul_(a, d));
		cong_mod_(mul_(sub_(d, b), mul_(a, d)), m, mul_(mul_(a, d), sub_(d, b)), m);
		lemma_eq_ref(m);
	}
	let temp_42_0 = (add_((mul_(b, c)), (mul_(c, c))));
	let temp_42_1 = (mul_((add_(b, c)), c));
	assert(eq_(temp_42_0, temp_42_1)) by {
		lemma_eq_sym(temp_42_1, temp_42_0);
		lemma_mul_dist(b, c, c);
	}
	let temp_43_0 = (add_(c, (add_(b, c))));
	let temp_43_1 = (add_(c, (add_(c, b))));
	assert(eq_(temp_43_0, temp_43_1)) by {
		cong_add_(c, add_(b, c), c, add_(c, b));
		lemma_add_comm(b, c);
		lemma_eq_ref(c);
	}
	let temp_44_0 = (sub_((add_(c, b)), (add_(a, c))));
	let temp_44_1 = (sub_((add_(b, c)), (add_(a, c))));
	assert(eq_(temp_44_0, temp_44_1)) by {
		cong_sub_(add_(c, b), add_(a, c), add_(b, c), add_(a, c));
		lemma_add_comm(c, b);
		lemma_eq_ref(add_(a, c));
	}
	let temp_45_0 = (mul_((mul_((mod_(d, m)), a)), (mul_(b, b))));
	let temp_45_1 = (mul_((mod_(d, m)), (mul_(a, (mul_(b, b))))));
	assert(eq_(temp_45_0, temp_45_1)) by {
		lemma_mul_assoc(mod_(d, m), a, mul_(b, b));
		lemma_eq_sym(temp_45_1, temp_45_0);
	}
	let temp_46_0 = (mul_((mul_(c, c)), (sub_(a, c))));
	let temp_46_1 = (mul_((sub_(a, c)), (mul_(c, c))));
	assert(eq_(temp_46_0, temp_46_1)) by {
		lemma_mul_comm(mul_(c, c), sub_(a, c));
	}
	let temp_47_0 = (mul_((add_(c, b)), (mul_(c, d))));
	let temp_47_1 = (mul_((mul_((add_(c, b)), c)), d));
	assert(eq_(temp_47_0, temp_47_1)) by {
		lemma_mul_assoc(add_(c, b), c, d);
	}
	let temp_48_0 = (mul_((mul_(c, c)), (mul_(a, c))));
	let temp_48_1 = (mul_(c, (mul_(c, (mul_(a, c))))));
	assert(eq_(temp_48_0, temp_48_1)) by {
		lemma_eq_sym(temp_48_1, temp_48_0);
		lemma_mul_assoc(c, c, mul_(a, c));
	}
	let temp_49_0 = (mul_((mul_(a, d)), (mod_((mul_(b, a)), m))));
	let temp_49_1 = (mul_((mul_(d, a)), (mod_((mul_(b, a)), m))));
	assert(eq_(temp_49_0, temp_49_1)) by {
		lemma_mul_comm(a, d);
		cong_mul_(mul_(a, d), mod_(mul_(b, a), m), mul_(d, a), mod_(mul_(b, a), m));
		lemma_eq_ref(mod_(mul_(b, a), m));
	}
	let temp_50_0 = (add_((mod_((mul_(b, (mod_(d, m)))), m)), (mul_(a, d))));
	let temp_50_1 = (add_((mod_((mul_((mod_(d, m)), b)), m)), (mul_(a, d))));
	assert(eq_(temp_50_0, temp_50_1)) by {
		lemma_mul_comm(b, mod_(d, m));
		cong_add_(mod_(mul_(b, mod_(d, m)), m), mul_(a, d), mod_(mul_(mod_(d, m), b), m), mul_(a, d));
		lemma_eq_ref(m);
		cong_mod_(mul_(b, mod_(d, m)), m, mul_(mod_(d, m), b), m);
		lemma_eq_ref(mul_(a, d));
	}
	let temp_51_0 = (mul_((sub_(a, (mod_(d, m)))), (mul_(c, a))));
	let temp_51_1 = (mul_((mul_(c, a)), (sub_(a, (mod_(d, m))))));
	assert(eq_(temp_51_0, temp_51_1)) by {
		lemma_mul_comm(sub_(a, mod_(d, m)), mul_(c, a));
	}
	let temp_52_0 = (mul_((mul_(a, b)), (mul_((mod_(c, m)), b))));
	let temp_52_1 = (mul_((mul_(a, b)), (mul_((mod_((add_(c, (mul_((mul_((add_(a, d)), (mul_(b, b)))), m)))), m)), b))));
	assert(eq_(temp_52_0, temp_52_1)) by {
		lemma_mod_mul_vanish(c, mul_(add_(a, d), mul_(b, b)), m);
		cong_mul_(mul_(a, b), mul_(mod_(c, m), b), mul_(a, b), mul_(mod_(add_(c, mul_(mul_(add_(a, d), mul_(b, b)), m)), m), b));
		lemma_eq_ref(b);
		lemma_eq_ref(mul_(a, b));
		cong_mul_(mod_(c, m), b, mod_(add_(c, mul_(mul_(add_(a, d), mul_(b, b)), m)), m), b);
	}
	let temp_53_0 = (mul_((mul_(d, b)), (mul_((mod_(d, m)), c))));
	let temp_53_1 = (mul_((mul_(d, b)), (mul_((mod_((add_(d, (mul_((mul_((mod_((mul_(a, a)), m)), (mul_(b, d)))), m)))), m)), c))));
	assert(eq_(temp_53_0, temp_53_1)) by {
		lemma_mod_mul_vanish(d, mul_(mod_(mul_(a, a), m), mul_(b, d)), m);
		cong_mul_(mul_(d, b), mul_(mod_(d, m), c), mul_(d, b), mul_(mod_(add_(d, mul_(mul_(mod_(mul_(a, a), m), mul_(b, d)), m)), m), c));
		lemma_eq_ref(c);
		lemma_eq_ref(mul_(d, b));
		cong_mul_(mod_(d, m), c, mod_(add_(d, mul_(mul_(mod_(mul_(a, a), m), mul_(b, d)), m)), m), c);
	}
	let temp_54_0 = (add_((mul_(d, d)), (mod_((mul_(b, b)), m))));
	let temp_54_1 = (add_((mul_(d, d)), (mod_((mul_(b, b)), m))));
	assert(eq_(temp_54_0, temp_54_1)) by {
		lemma_eq_ref(temp_54_0);
	}
	let temp_55_0 = (mul_((mul_(b, a)), (add_((mod_(c, m)), c))));
	let temp_55_1 = (add_((mul_((mul_(b, a)), (mod_(c, m)))), (mul_((mul_(b, a)), c))));
	assert(eq_(temp_55_0, temp_55_1)) by {
		lemma_mul_dist(mul_(b, a), mod_(c, m), c);
	}
	let temp_56_0 = (mul_((mul_(d, a)), (mul_(d, d))));
	let temp_56_1 = (mul_(d, (mul_(a, (mul_(d, d))))));
	assert(eq_(temp_56_0, temp_56_1)) by {
		lemma_eq_sym(temp_56_1, temp_56_0);
		lemma_mul_assoc(d, a, mul_(d, d));
	}
	let temp_57_0 = (mul_((mul_(b, d)), (add_(a, a))));
	let temp_57_1 = (mul_((add_(a, a)), (mul_(b, d))));
	assert(eq_(temp_57_0, temp_57_1)) by {
		lemma_mul_comm(mul_(b, d), add_(a, a));
	}
	let temp_58_0 = (sub_((mul_(c, d)), (add_(b, b))));
	let temp_58_1 = (sub_((mul_(c, d)), (add_(b, b))));
	assert(eq_(temp_58_0, temp_58_1)) by {
		lemma_eq_ref(temp_58_0);
	}
	let temp_59_0 = (mul_((add_(a, d)), (mul_(d, b))));
	let temp_59_1 = (mul_((mul_((add_(a, d)), d)), b));
	assert(eq_(temp_59_0, temp_59_1)) by {
		lemma_mul_assoc(add_(a, d), d, b);
	}
	let temp_60_0 = (mul_((add_(a, a)), (mul_(a, b))));
	let temp_60_1 = (mul_((mul_((add_(a, a)), a)), b));
	assert(eq_(temp_60_0, temp_60_1)) by {
		lemma_mul_assoc(add_(a, a), a, b);
	}
	let temp_61_0 = (add_((mul_(a, (mod_(a, m)))), (mul_(c, b))));
	let temp_61_1 = (add_((mul_(a, (mod_(a, m)))), (mul_(b, c))));
	assert(eq_(temp_61_0, temp_61_1)) by {
		lemma_mul_comm(c, b);
		cong_add_(mul_(a, mod_(a, m)), mul_(c, b), mul_(a, mod_(a, m)), mul_(b, c));
		lemma_eq_ref(mul_(a, mod_(a, m)));
	}
	let temp_62_0 = (mul_((mul_((mod_(c, m)), b)), (mul_((mod_(a, m)), (mod_(a, m))))));
	let temp_62_1 = (mul_((mul_((mod_((add_((mul_((mul_((mul_(c, b)), (mul_(b, d)))), m)), c)), m)), b)), (mul_((mod_(a, m)), (mod_(a, m))))));
	assert(eq_(temp_62_0, temp_62_1)) by {
		lemma_mul_comm(mod_(a, m), mod_(a, m));
		lemma_mod_mul_vanish(c, mul_(mul_(c, b), mul_(b, d)), m);
		cong_mul_(mul_(mod_(c, m), b), mul_(mod_(a, m), mod_(a, m)), mul_(mod_(add_(mul_(mul_(mul_(c, b), mul_(b, d)), m), c), m), b), mul_(mod_(a, m), mod_(a, m)));
		lemma_eq_ref(b);
		cong_mul_(mod_(c, m), b, mod_(add_(mul_(mul_(mul_(c, b), mul_(b, d)), m), c), m), b);
	}
	let temp_63_0 = (mul_((mul_(d, c)), (mul_(d, b))));
	let temp_63_1 = (mul_(d, (mul_(c, (mul_(d, b))))));
	assert(eq_(temp_63_0, temp_63_1)) by {
		lemma_eq_sym(temp_63_1, temp_63_0);
		lemma_mul_assoc(d, c, mul_(d, b));
	}
	let temp_64_0 = (mul_((mul_((mod_(c, m)), c)), (mul_(c, c))));
	let temp_64_1 = (mul_((mul_((mod_((add_((mul_((mul_((mul_(d, d)), (mul_((mod_(b, m)), b)))), m)), c)), m)), c)), (mul_(c, c))));
	assert(eq_(temp_64_0, temp_64_1)) by {
		lemma_mul_comm(c, c);
		lemma_mod_mul_vanish(c, mul_(mul_(d, d), mul_(mod_(b, m), b)), m);
		cong_mul_(mul_(mod_(c, m), c), mul_(c, c), mul_(mod_(add_(mul_(mul_(mul_(d, d), mul_(mod_(b, m), b)), m), c), m), c), mul_(c, c));
		cong_mul_(mod_(c, m), c, mod_(add_(mul_(mul_(mul_(d, d), mul_(mod_(b, m), b)), m), c), m), c);
		lemma_eq_ref(c);
	}
	let temp_65_0 = (mul_((mul_(a, b)), (mul_(b, c))));
	let temp_65_1 = (mul_((mul_(b, a)), (mul_(b, c))));
	assert(eq_(temp_65_0, temp_65_1)) by {
		cong_mul_(mul_(a, b), mul_(b, c), mul_(b, a), mul_(b, c));
		lemma_mul_comm(a, b);
		lemma_eq_ref(mul_(b, c));
	}
	let temp_66_0 = (mul_((mul_(a, a)), (mul_(d, d))));
	let temp_66_1 = (mul_((mul_(d, d)), (mul_(a, a))));
	assert(eq_(temp_66_0, temp_66_1)) by {
		lemma_mul_comm(mul_(a, a), mul_(d, d));
	}
	let temp_67_0 = (mul_((mul_(d, c)), (sub_(b, (mod_(c, m))))));
	let temp_67_1 = (mul_((mul_(d, c)), (sub_(b, (mod_((add_(c, (mul_((mul_((add_(a, d)), (mul_(d, b)))), m)))), m))))));
	assert(eq_(temp_67_0, temp_67_1)) by {
		lemma_mod_mul_vanish(c, mul_(add_(a, d), mul_(d, b)), m);
		cong_mul_(mul_(d, c), sub_(b, mod_(c, m)), mul_(d, c), sub_(b, mod_(add_(c, mul_(mul_(add_(a, d), mul_(d, b)), m)), m)));
		cong_sub_(b, mod_(c, m), b, mod_(add_(c, mul_(mul_(add_(a, d), mul_(d, b)), m)), m));
		lemma_eq_ref(mul_(d, c));
		lemma_eq_ref(b);
	}
	let temp_68_0 = (sub_((mul_(d, c)), (mul_((mod_(d, m)), c))));
	let temp_68_1 = (sub_((mul_(d, c)), (mul_(c, (mod_(d, m))))));
	assert(eq_(temp_68_0, temp_68_1)) by {
		cong_sub_(mul_(d, c), mul_(mod_(d, m), c), mul_(d, c), mul_(c, mod_(d, m)));
		lemma_mul_comm(mod_(d, m), c);
		lemma_eq_ref(mul_(d, c));
	}
	let temp_69_0 = (mod_((mul_((mul_(c, a)), (mul_(d, (mod_(b, m)))))), m));
	let temp_69_1 = (mod_((mul_((mul_(c, a)), (mul_(d, (mod_((add_((mul_((mul_((mul_(b, a)), (mul_(as_elem(34), b)))), m)), b)), m)))))), m));
	assert(eq_(temp_69_0, temp_69_1)) by {
		lemma_mod_mul_vanish(b, mul_(mul_(b, a), mul_(as_elem(34), b)), m);
		cong_mod_(mul_(mul_(c, a), mul_(d, mod_(b, m))), m, mul_(mul_(c, a), mul_(d, mod_(add_(mul_(mul_(mul_(b, a), mul_(as_elem(34), b)), m), b), m))), m);
		lemma_eq_ref(d);
		lemma_eq_ref(mul_(c, a));
		cong_mul_(mul_(c, a), mul_(d, mod_(b, m)), mul_(c, a), mul_(d, mod_(add_(mul_(mul_(mul_(b, a), mul_(as_elem(34), b)), m), b), m)));
		cong_mul_(d, mod_(b, m), d, mod_(add_(mul_(mul_(mul_(b, a), mul_(as_elem(34), b)), m), b), m));
		lemma_eq_ref(m);
	}
	let temp_70_0 = (add_((add_(a, (mod_(b, m)))), (mul_(a, c))));
	let temp_70_1 = (add_((add_(a, (mod_((add_((mul_((mod_((add_((mul_(c, c)), (mod_((mul_(d, a)), m)))), m)), m)), b)), m)))), (mul_(a, c))));
	assert(eq_(temp_70_0, temp_70_1)) by {
		lemma_mod_mul_vanish(b, mod_(add_(mul_(c, c), mod_(mul_(d, a), m)), m), m);
		cong_add_(add_(a, mod_(b, m)), mul_(a, c), add_(a, mod_(add_(mul_(mod_(add_(mul_(c, c), mod_(mul_(d, a), m)), m), m), b), m)), mul_(a, c));
		lemma_eq_ref(a);
		cong_add_(a, mod_(b, m), a, mod_(add_(mul_(mod_(add_(mul_(c, c), mod_(mul_(d, a), m)), m), m), b), m));
		lemma_eq_ref(mul_(a, c));
	}
	let temp_71_0 = (mod_((mul_((mul_((mod_(d, m)), a)), (sub_(d, b)))), m));
	let temp_71_1 = (mod_((mul_((mul_(a, (mod_(d, m)))), (sub_(d, b)))), m));
	assert(eq_(temp_71_0, temp_71_1)) by {
		lemma_mul_comm(mod_(d, m), a);
		cong_mod_(mul_(mul_(mod_(d, m), a), sub_(d, b)), m, mul_(mul_(a, mod_(d, m)), sub_(d, b)), m);
		lemma_eq_ref(sub_(d, b));
		cong_mul_(mul_(mod_(d, m), a), sub_(d, b), mul_(a, mod_(d, m)), sub_(d, b));
		lemma_eq_ref(m);
	}
	let temp_72_0 = (mul_((add_(a, a)), (sub_(a, a))));
	let temp_72_1 = (mul_((add_(a, a)), (sub_(a, a))));
	assert(eq_(temp_72_0, temp_72_1)) by {
		lemma_eq_ref(temp_72_0);
	}
	let temp_73_0 = (add_((mul_(d, b)), (mul_(c, c))));
	let temp_73_1 = (add_((mul_(d, b)), (mul_(c, c))));
	assert(eq_(temp_73_0, temp_73_1)) by {
		lemma_eq_ref(temp_73_0);
	}
	let temp_74_0 = (mul_((mul_(d, b)), (sub_(a, b))));
	let temp_74_1 = (mul_((sub_(a, b)), (mul_(d, b))));
	assert(eq_(temp_74_0, temp_74_1)) by {
		lemma_mul_comm(mul_(d, b), sub_(a, b));
	}
	let temp_75_0 = (mul_((sub_(b, d)), (mod_((mul_(c, d)), m))));
	let temp_75_1 = (mul_((sub_(b, d)), (mod_((mul_(d, c)), m))));
	assert(eq_(temp_75_0, temp_75_1)) by {
		lemma_mul_comm(c, d);
		cong_mul_(sub_(b, d), mod_(mul_(c, d), m), sub_(b, d), mod_(mul_(d, c), m));
		lemma_eq_ref(sub_(b, d));
		cong_mod_(mul_(c, d), m, mul_(d, c), m);
		lemma_eq_ref(m);
	}
	let temp_76_0 = (mul_((mul_(b, c)), (add_(d, c))));
	let temp_76_1 = (mul_(b, (mul_(c, (add_(d, c))))));
	assert(eq_(temp_76_0, temp_76_1)) by {
		lemma_eq_sym(temp_76_1, temp_76_0);
		lemma_mul_assoc(b, c, add_(d, c));
	}
	let temp_77_0 = (mul_((mul_(d, d)), (sub_(d, d))));
	let temp_77_1 = (mul_((mul_(d, d)), (sub_(d, d))));
	assert(eq_(temp_77_0, temp_77_1)) by {
		lemma_eq_ref(temp_77_0);
	}
	let temp_78_0 = (add_((mul_(d, (mod_(b, m)))), (mul_(c, d))));
	let temp_78_1 = (add_((mul_(c, d)), (mul_(d, (mod_(b, m))))));
	assert(eq_(temp_78_0, temp_78_1)) by {
		lemma_add_comm(mul_(d, mod_(b, m)), mul_(c, d));
	}
	let temp_79_0 = (mul_((mul_(c, d)), (mod_((mul_(a, a)), m))));
	let temp_79_1 = (mul_((mul_(c, d)), (mod_((add_((mul_(a, a)), (mul_((mul_((mul_(a, a)), (mul_(b, a)))), m)))), m))));
	assert(eq_(temp_79_0, temp_79_1)) by {
		lemma_mod_mul_vanish(mul_(a, a), mul_(mul_(a, a), mul_(b, a)), m);
		cong_mul_(mul_(c, d), mod_(mul_(a, a), m), mul_(c, d), mod_(add_(mul_(a, a), mul_(mul_(mul_(a, a), mul_(b, a)), m)), m));
		lemma_eq_ref(mul_(c, d));
	}
	let temp_80_0 = (mul_((mul_(b, b)), (add_(b, a))));
	let temp_80_1 = (mul_((add_(b, a)), (mul_(b, b))));
	assert(eq_(temp_80_0, temp_80_1)) by {
		lemma_mul_comm(mul_(b, b), add_(b, a));
	}
	let temp_81_0 = (mod_((mul_((mul_(a, b)), (sub_(d, (mod_(d, m)))))), m));
	let temp_81_1 = (mod_((mul_(a, (mul_(b, (sub_(d, (mod_(d, m)))))))), m));
	assert(eq_(temp_81_0, temp_81_1)) by {
		lemma_mul_assoc(a, b, sub_(d, mod_(d, m)));
		cong_mod_(mul_(mul_(a, b), sub_(d, mod_(d, m))), m, mul_(a, mul_(b, sub_(d, mod_(d, m)))), m);
		lemma_eq_sym(mul_(a, mul_(b, sub_(d, mod_(d, m)))), mul_(mul_(a, b), sub_(d, mod_(d, m))));
		lemma_eq_ref(m);
	}
	let temp_82_0 = (mul_((mul_(d, c)), (mod_((mul_(c, d)), m))));
	let temp_82_1 = (mul_((mul_(d, c)), (mod_((add_((mul_(c, d)), (mul_((add_((mod_((mul_((mod_(c, m)), a)), m)), (mul_(c, b)))), m)))), m))));
	assert(eq_(temp_82_0, temp_82_1)) by {
		lemma_mod_mul_vanish(mul_(c, d), add_(mod_(mul_(mod_(c, m), a), m), mul_(c, b)), m);
		cong_mul_(mul_(d, c), mod_(mul_(c, d), m), mul_(d, c), mod_(add_(mul_(c, d), mul_(add_(mod_(mul_(mod_(c, m), a), m), mul_(c, b)), m)), m));
		lemma_eq_ref(mul_(d, c));
	}
	let temp_83_0 = (mul_((mul_((mod_(d, m)), c)), (mul_(as_elem(1), (mod_(c, m))))));
	let temp_83_1 = (mul_((mod_(d, m)), (mul_(c, (mul_(as_elem(1), (mod_(c, m))))))));
	assert(eq_(temp_83_0, temp_83_1)) by {
		lemma_mul_assoc(mod_(d, m), c, mul_(as_elem(1), mod_(c, m)));
		lemma_eq_sym(temp_83_1, temp_83_0);
	}
	let temp_84_0 = (mod_((mul_(c, (mul_(a, as_elem(55))))), m));
	let temp_84_1 = (mod_((mul_((mul_(a, as_elem(55))), c)), m));
	assert(eq_(temp_84_0, temp_84_1)) by {
		lemma_mul_comm(c, mul_(a, as_elem(55)));
		cong_mod_(mul_(c, mul_(a, as_elem(55))), m, mul_(mul_(a, as_elem(55)), c), m);
		lemma_eq_ref(m);
	}
	let temp_85_0 = (mul_((mul_(b, c)), (mul_(a, d))));
	let temp_85_1 = (mul_((mul_(a, d)), (mul_(b, c))));
	assert(eq_(temp_85_0, temp_85_1)) by {
		lemma_mul_comm(mul_(b, c), mul_(a, d));
	}
	let temp_86_0 = (mul_((mul_(a, d)), (mul_(c, c))));
	let temp_86_1 = (mul_((mul_(a, d)), (mul_(c, c))));
	assert(eq_(temp_86_0, temp_86_1)) by {
		lemma_eq_ref(temp_86_0);
	}
	let temp_87_0 = (sub_((mul_(a, (mod_(d, m)))), (mul_(d, c))));
	let temp_87_1 = (sub_((mul_(a, (mod_((add_(d, (mul_((mul_((mul_(as_elem(22), a)), (mul_(d, as_elem(28))))), m)))), m)))), (mul_(d, c))));
	assert(eq_(temp_87_0, temp_87_1)) by {
		lemma_mod_mul_vanish(d, mul_(mul_(as_elem(22), a), mul_(d, as_elem(28))), m);
		cong_sub_(mul_(a, mod_(d, m)), mul_(d, c), mul_(a, mod_(add_(d, mul_(mul_(mul_(as_elem(22), a), mul_(d, as_elem(28))), m)), m)), mul_(d, c));
		lemma_eq_ref(a);
		cong_mul_(a, mod_(d, m), a, mod_(add_(d, mul_(mul_(mul_(as_elem(22), a), mul_(d, as_elem(28))), m)), m));
		lemma_eq_ref(mul_(d, c));
	}
	let temp_88_0 = (mul_((mul_(c, b)), (mul_(c, b))));
	let temp_88_1 = (mul_((mul_((mul_(c, b)), c)), b));
	assert(eq_(temp_88_0, temp_88_1)) by {
		lemma_mul_assoc(mul_(c, b), c, b);
	}
	let temp_89_0 = (mul_((mul_(d, (mod_(c, m)))), (mul_(d, d))));
	let temp_89_1 = (mul_((mul_((mod_(c, m)), d)), (mul_(d, d))));
	assert(eq_(temp_89_0, temp_89_1)) by {
		cong_mul_(mul_(d, mod_(c, m)), mul_(d, d), mul_(mod_(c, m), d), mul_(d, d));
		lemma_mul_comm(d, mod_(c, m));
		lemma_mul_comm(d, d);
	}
	let temp_90_0 = (mul_((sub_((mod_(b, m)), b)), (mul_(b, a))));
	let temp_90_1 = (mul_((mul_((sub_((mod_(b, m)), b)), b)), a));
	assert(eq_(temp_90_0, temp_90_1)) by {
		lemma_mul_assoc(sub_(mod_(b, m), b), b, a);
	}
	let temp_91_0 = (mul_((mul_(a, a)), (mul_(b, b))));
	let temp_91_1 = (mul_((mul_((mul_(a, a)), b)), b));
	assert(eq_(temp_91_0, temp_91_1)) by {
		lemma_mul_assoc(mul_(a, a), b, b);
	}
	let temp_92_0 = (mul_((add_(a, b)), (mul_(c, (mod_(c, m))))));
	let temp_92_1 = (mul_((mul_((add_(a, b)), c)), (mod_(c, m))));
	assert(eq_(temp_92_0, temp_92_1)) by {
		lemma_mul_assoc(add_(a, b), c, mod_(c, m));
	}
	let temp_93_0 = (mul_(c, (mul_(b, b))));
	let temp_93_1 = (mul_(c, (mul_(b, b))));
	assert(eq_(temp_93_0, temp_93_1)) by {
		lemma_eq_ref(temp_93_0);
	}

}

} // verus!