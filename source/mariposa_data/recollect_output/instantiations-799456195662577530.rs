use builtin_macros::*;
// use builtin::*;
mod nl_basics;
use crate::nl_basics::*;
verus! {

pub proof fn free_0(a: Elem, b: Elem, c: Elem, d: Elem, m: Elem)
{
	let temp_0_0 = (mul_((mul_(c, a)), (mul_(b, a))));
	let temp_0_1 = (mul_((mul_(b, a)), (mul_(c, a))));
	assert(eq_(temp_0_0, temp_0_1)) by {
		lemma_mul_comm(mul_(c, a), mul_(b, a));
	}
	let temp_1_0 = (mul_((mul_(b, a)), (mul_(d, a))));
	let temp_1_1 = (mul_(b, (mul_(a, (mul_(d, a))))));
	assert(eq_(temp_1_0, temp_1_1)) by {
		lemma_eq_sym(temp_1_1, temp_1_0);
		lemma_mul_assoc(b, a, mul_(d, a));
	}
	let temp_2_0 = (mul_((mul_(d, c)), (mul_(a, c))));
	let temp_2_1 = (mul_((mul_((mul_(d, c)), a)), c));
	assert(eq_(temp_2_0, temp_2_1)) by {
		lemma_mul_assoc(mul_(d, c), a, c);
	}
	let temp_3_0 = (add_((mul_(a, c)), (add_(a, c))));
	let temp_3_1 = (add_((mul_(a, c)), (add_(c, a))));
	assert(eq_(temp_3_0, temp_3_1)) by {
		cong_add_(mul_(a, c), add_(a, c), mul_(a, c), add_(c, a));
		lemma_add_comm(a, c);
		lemma_eq_ref(mul_(a, c));
	}
	let temp_4_0 = (mul_((mul_(c, d)), (mul_(b, b))));
	let temp_4_1 = (mul_((mul_(d, c)), (mul_(b, b))));
	assert(eq_(temp_4_0, temp_4_1)) by {
		cong_mul_(mul_(c, d), mul_(b, b), mul_(d, c), mul_(b, b));
		lemma_mul_comm(c, d);
		lemma_mul_comm(b, b);
	}
	let temp_5_0 = (mul_((mul_(b, b)), (sub_(c, d))));
	let temp_5_1 = (mul_(b, (mul_(b, (sub_(c, d))))));
	assert(eq_(temp_5_0, temp_5_1)) by {
		lemma_eq_sym(temp_5_1, temp_5_0);
		lemma_mul_assoc(b, b, sub_(c, d));
	}
	let temp_6_0 = (add_((mul_(c, b)), (add_(d, a))));
	let temp_6_1 = (add_((mul_(b, c)), (add_(d, a))));
	assert(eq_(temp_6_0, temp_6_1)) by {
		cong_add_(mul_(c, b), add_(d, a), mul_(b, c), add_(d, a));
		lemma_mul_comm(c, b);
		lemma_eq_ref(add_(d, a));
	}
	let temp_7_0 = (mul_((mod_((mul_(a, b)), m)), (mul_(c, c))));
	let temp_7_1 = (mul_((mod_((mul_(b, a)), m)), (mul_(c, c))));
	assert(eq_(temp_7_0, temp_7_1)) by {
		lemma_mul_comm(a, b);
		lemma_mul_comm(c, c);
		cong_mul_(mod_(mul_(a, b), m), mul_(c, c), mod_(mul_(b, a), m), mul_(c, c));
		cong_mod_(mul_(a, b), m, mul_(b, a), m);
		lemma_eq_ref(m);
	}
	let temp_8_0 = (mul_((mul_(c, d)), (mod_((mul_(c, (mod_(c, m)))), m))));
	let temp_8_1 = (mul_(c, (mul_(d, (mod_((mul_(c, (mod_(c, m)))), m))))));
	assert(eq_(temp_8_0, temp_8_1)) by {
		lemma_mul_assoc(c, d, mod_(mul_(c, mod_(c, m)), m));
		lemma_eq_sym(temp_8_1, temp_8_0);
	}
	let temp_9_0 = (mul_((mod_((mul_(d, d)), m)), (mul_(b, a))));
	let temp_9_1 = (mul_((mul_(b, a)), (mod_((mul_(d, d)), m))));
	assert(eq_(temp_9_0, temp_9_1)) by {
		lemma_mul_comm(mod_(mul_(d, d), m), mul_(b, a));
	}
	let temp_10_0 = (mul_((mul_((mod_(b, m)), c)), (sub_(b, a))));
	let temp_10_1 = (mul_((mod_(b, m)), (mul_(c, (sub_(b, a))))));
	assert(eq_(temp_10_0, temp_10_1)) by {
		lemma_mul_assoc(mod_(b, m), c, sub_(b, a));
		lemma_eq_sym(temp_10_1, temp_10_0);
	}
	let temp_11_0 = (mul_((mul_(b, b)), (mul_(a, d))));
	let temp_11_1 = (mul_((mul_((mul_(b, b)), a)), d));
	assert(eq_(temp_11_0, temp_11_1)) by {
		lemma_mul_assoc(mul_(b, b), a, d);
	}
	let temp_12_0 = (mul_((mod_((mul_(d, (mod_(d, m)))), m)), (mul_(d, c))));
	let temp_12_1 = (mul_((mul_((mod_((mul_(d, (mod_(d, m)))), m)), d)), c));
	assert(eq_(temp_12_0, temp_12_1)) by {
		lemma_mul_assoc(mod_(mul_(d, mod_(d, m)), m), d, c);
	}
	let temp_13_0 = (mul_((mul_(a, c)), (mul_(d, c))));
	let temp_13_1 = (mul_((mul_(c, a)), (mul_(d, c))));
	assert(eq_(temp_13_0, temp_13_1)) by {
		cong_mul_(mul_(a, c), mul_(d, c), mul_(c, a), mul_(d, c));
		lemma_mul_comm(a, c);
		lemma_eq_ref(mul_(d, c));
	}
	let temp_14_0 = (mul_((mul_(a, d)), (mul_((mod_(a, m)), c))));
	let temp_14_1 = (mul_((mul_(a, d)), (mul_((mod_((add_(a, (mul_((mod_((mul_((mul_((mod_(c, m)), c)), (mul_(a, a)))), m)), m)))), m)), c))));
	assert(eq_(temp_14_0, temp_14_1)) by {
		lemma_mod_mul_vanish(a, mod_(mul_(mul_(mod_(c, m), c), mul_(a, a)), m), m);
		cong_mul_(mul_(a, d), mul_(mod_(a, m), c), mul_(a, d), mul_(mod_(add_(a, mul_(mod_(mul_(mul_(mod_(c, m), c), mul_(a, a)), m), m)), m), c));
		lemma_eq_ref(mul_(a, d));
		cong_mul_(mod_(a, m), c, mod_(add_(a, mul_(mod_(mul_(mul_(mod_(c, m), c), mul_(a, a)), m), m)), m), c);
		lemma_eq_ref(c);
	}
	let temp_15_0 = (mul_((sub_(c, d)), (mul_(b, c))));
	let temp_15_1 = (mul_((mul_(b, c)), (sub_(c, d))));
	assert(eq_(temp_15_0, temp_15_1)) by {
		lemma_mul_comm(sub_(c, d), mul_(b, c));
	}
	let temp_16_0 = (mul_((mul_(d, b)), (mul_(a, as_elem(73)))));
	let temp_16_1 = (mul_((mul_(d, b)), (mul_(as_elem(73), a))));
	assert(eq_(temp_16_0, temp_16_1)) by {
		lemma_mul_comm(a, as_elem(73));
		cong_mul_(mul_(d, b), mul_(a, as_elem(73)), mul_(d, b), mul_(as_elem(73), a));
		lemma_eq_ref(mul_(d, b));
	}
	let temp_17_0 = (mul_((mul_(a, b)), (mul_(d, b))));
	let temp_17_1 = (mul_(a, (mul_(b, (mul_(d, b))))));
	assert(eq_(temp_17_0, temp_17_1)) by {
		lemma_eq_sym(temp_17_1, temp_17_0);
		lemma_mul_assoc(a, b, mul_(d, b));
	}
	let temp_18_0 = (mul_((sub_(a, d)), (mod_(c, m))));
	let temp_18_1 = (mul_((mod_(c, m)), (sub_(a, d))));
	assert(eq_(temp_18_0, temp_18_1)) by {
		lemma_mul_comm(sub_(a, d), mod_(c, m));
	}
	let temp_19_0 = (mul_((mul_(b, (mod_(d, m)))), (mul_(c, b))));
	let temp_19_1 = (mul_((mul_(c, b)), (mul_(b, (mod_(d, m))))));
	assert(eq_(temp_19_0, temp_19_1)) by {
		lemma_mul_comm(mul_(b, mod_(d, m)), mul_(c, b));
	}
	let temp_20_0 = (mul_((mul_(b, d)), (mul_(c, b))));
	let temp_20_1 = (mul_((mul_(d, b)), (mul_(c, b))));
	assert(eq_(temp_20_0, temp_20_1)) by {
		cong_mul_(mul_(b, d), mul_(c, b), mul_(d, b), mul_(c, b));
		lemma_mul_comm(b, d);
		lemma_eq_ref(mul_(c, b));
	}
	let temp_21_0 = (mul_((sub_(c, d)), (mul_(b, d))));
	let temp_21_1 = (mul_((sub_(c, d)), (mul_(d, b))));
	assert(eq_(temp_21_0, temp_21_1)) by {
		cong_mul_(sub_(c, d), mul_(b, d), sub_(c, d), mul_(d, b));
		lemma_mul_comm(b, d);
		lemma_eq_ref(sub_(c, d));
	}
	let temp_22_0 = (mul_((add_((mod_(a, m)), a)), (mod_((mul_(d, b)), m))));
	let temp_22_1 = (add_((mul_((mod_(a, m)), (mod_((mul_(d, b)), m)))), (mul_(a, (mod_((mul_(d, b)), m))))));
	assert(eq_(temp_22_0, temp_22_1)) by {
		lemma_mul_dist(mod_(a, m), a, mod_(mul_(d, b), m));
	}
	let temp_23_0 = (mul_((sub_(d, as_elem(23))), (mul_(c, a))));
	let temp_23_1 = (mul_((mul_((sub_(d, as_elem(23))), c)), a));
	assert(eq_(temp_23_0, temp_23_1)) by {
		lemma_mul_assoc(sub_(d, as_elem(23)), c, a);
	}
	let temp_24_0 = (mul_((mul_(d, c)), (add_((mod_(b, m)), (mod_(b, m))))));
	let temp_24_1 = (mul_(d, (mul_(c, (add_((mod_(b, m)), (mod_(b, m))))))));
	assert(eq_(temp_24_0, temp_24_1)) by {
		lemma_mul_assoc(d, c, add_(mod_(b, m), mod_(b, m)));
		lemma_eq_sym(temp_24_1, temp_24_0);
	}
	let temp_25_0 = (mul_((sub_(d, c)), (sub_((mod_(d, m)), d))));
	let temp_25_1 = (sub_((mul_(d, (sub_((mod_(d, m)), d)))), (mul_(c, (sub_((mod_(d, m)), d))))));
	assert(eq_(temp_25_0, temp_25_1)) by {
		lemma_mul_dist(sub_(mod_(d, m), d), d, c);
	}
	let temp_26_0 = (mul_((mul_((mod_(c, m)), c)), (mul_(d, a))));
	let temp_26_1 = (mul_((mul_(c, (mod_(c, m)))), (mul_(d, a))));
	assert(eq_(temp_26_0, temp_26_1)) by {
		lemma_mul_comm(mod_(c, m), c);
		cong_mul_(mul_(mod_(c, m), c), mul_(d, a), mul_(c, mod_(c, m)), mul_(d, a));
		lemma_eq_ref(mul_(d, a));
	}
	let temp_27_0 = (add_((mul_(d, (mod_(a, m)))), (mul_(c, b))));
	let temp_27_1 = (add_((mul_(d, (mod_((add_(a, (mul_((add_((mod_((add_(c, b)), m)), (mul_(a, (mod_(a, m)))))), m)))), m)))), (mul_(c, b))));
	assert(eq_(temp_27_0, temp_27_1)) by {
		lemma_mod_mul_vanish(a, add_(mod_(add_(c, b), m), mul_(a, mod_(a, m))), m);
		cong_add_(mul_(d, mod_(a, m)), mul_(c, b), mul_(d, mod_(add_(a, mul_(add_(mod_(add_(c, b), m), mul_(a, mod_(a, m))), m)), m)), mul_(c, b));
		lemma_eq_ref(d);
		cong_mul_(d, mod_(a, m), d, mod_(add_(a, mul_(add_(mod_(add_(c, b), m), mul_(a, mod_(a, m))), m)), m));
		lemma_eq_ref(mul_(c, b));
	}
	let temp_28_0 = (mul_((mul_(b, a)), (mul_(c, b))));
	let temp_28_1 = (mul_((mul_(b, a)), (mul_(b, c))));
	assert(eq_(temp_28_0, temp_28_1)) by {
		cong_mul_(mul_(b, a), mul_(c, b), mul_(b, a), mul_(b, c));
		lemma_mul_comm(c, b);
		lemma_eq_ref(mul_(b, a));
	}
	let temp_29_0 = (mod_((sub_((mul_(a, c)), (mod_((mul_(c, a)), m)))), m));
	let temp_29_1 = (mod_((sub_((mul_(a, c)), (mod_((mul_(a, c)), m)))), m));
	assert(eq_(temp_29_0, temp_29_1)) by {
		lemma_mul_comm(c, a);
		cong_mod_(sub_(mul_(a, c), mod_(mul_(c, a), m)), m, sub_(mul_(a, c), mod_(mul_(a, c), m)), m);
		lemma_eq_ref(m);
		cong_sub_(mul_(a, c), mod_(mul_(c, a), m), mul_(a, c), mod_(mul_(a, c), m));
		lemma_eq_ref(mul_(a, c));
		cong_mod_(mul_(c, a), m, mul_(a, c), m);
	}
	let temp_30_0 = (sub_((mul_(b, c)), (add_(b, d))));
	let temp_30_1 = (sub_((mul_(b, c)), (add_(d, b))));
	assert(eq_(temp_30_0, temp_30_1)) by {
		cong_sub_(mul_(b, c), add_(b, d), mul_(b, c), add_(d, b));
		lemma_add_comm(b, d);
		lemma_eq_ref(mul_(b, c));
	}
	let temp_31_0 = (mul_((mul_(b, d)), (add_(b, c))));
	let temp_31_1 = (add_((mul_((mul_(b, d)), b)), (mul_((mul_(b, d)), c))));
	assert(eq_(temp_31_0, temp_31_1)) by {
		lemma_mul_dist(mul_(b, d), b, c);
	}
	let temp_32_0 = (mod_((mul_((mul_(b, (mod_(a, m)))), (add_(a, d)))), m));
	let temp_32_1 = (mod_((mul_(b, (mul_((mod_(a, m)), (add_(a, d)))))), m));
	assert(eq_(temp_32_0, temp_32_1)) by {
		lemma_mul_assoc(b, mod_(a, m), add_(a, d));
		cong_mod_(mul_(mul_(b, mod_(a, m)), add_(a, d)), m, mul_(b, mul_(mod_(a, m), add_(a, d))), m);
		lemma_eq_sym(mul_(b, mul_(mod_(a, m), add_(a, d))), mul_(mul_(b, mod_(a, m)), add_(a, d)));
		lemma_eq_ref(m);
	}
	let temp_33_0 = (mul_((mul_(d, c)), (sub_(c, c))));
	let temp_33_1 = (mul_((sub_(c, c)), (mul_(d, c))));
	assert(eq_(temp_33_0, temp_33_1)) by {
		lemma_mul_comm(mul_(d, c), sub_(c, c));
	}
	let temp_34_0 = (mul_((mul_(a, d)), (mul_(a, as_elem(15)))));
	let temp_34_1 = (mul_(a, (mul_(d, (mul_(a, as_elem(15)))))));
	assert(eq_(temp_34_0, temp_34_1)) by {
		lemma_eq_sym(temp_34_1, temp_34_0);
		lemma_mul_assoc(a, d, mul_(a, as_elem(15)));
	}
	let temp_35_0 = (mul_((sub_(b, d)), (mul_(a, b))));
	let temp_35_1 = (sub_((mul_(b, (mul_(a, b)))), (mul_(d, (mul_(a, b))))));
	assert(eq_(temp_35_0, temp_35_1)) by {
		lemma_mul_dist(mul_(a, b), b, d);
	}
	let temp_36_0 = (mul_((mul_(a, b)), (mul_(d, d))));
	let temp_36_1 = (mul_((mul_(d, d)), (mul_(a, b))));
	assert(eq_(temp_36_0, temp_36_1)) by {
		lemma_mul_comm(mul_(a, b), mul_(d, d));
	}
	let temp_37_0 = (mul_((mul_(b, a)), (mul_(c, b))));
	let temp_37_1 = (mul_(b, (mul_(a, (mul_(c, b))))));
	assert(eq_(temp_37_0, temp_37_1)) by {
		lemma_eq_sym(temp_37_1, temp_37_0);
		lemma_mul_assoc(b, a, mul_(c, b));
	}
	let temp_38_0 = (mul_((mul_((mod_(b, m)), c)), (mul_((mod_(c, m)), (mod_(c, m))))));
	let temp_38_1 = (mul_((mul_((mod_(b, m)), c)), (mul_((mod_((sub_(c, (mul_((mul_((add_((mod_(as_elem(34), m)), c)), (mul_(d, b)))), m)))), m)), (mod_(c, m))))));
	assert(eq_(temp_38_0, temp_38_1)) by {
		lemma_mod_mul_vanish(c, mul_(add_(mod_(as_elem(34), m), c), mul_(d, b)), m);
		cong_mul_(mul_(mod_(b, m), c), mul_(mod_(c, m), mod_(c, m)), mul_(mod_(b, m), c), mul_(mod_(sub_(c, mul_(mul_(add_(mod_(as_elem(34), m), c), mul_(d, b)), m)), m), mod_(c, m)));
		lemma_eq_ref(mod_(c, m));
		lemma_eq_ref(mul_(mod_(b, m), c));
		cong_mul_(mod_(c, m), mod_(c, m), mod_(sub_(c, mul_(mul_(add_(mod_(as_elem(34), m), c), mul_(d, b)), m)), m), mod_(c, m));
	}
	let temp_39_0 = (add_((mod_((mul_(c, c)), m)), (mul_(a, c))));
	let temp_39_1 = (add_((mod_((sub_((mul_(c, c)), (mul_((mul_((mul_(c, d)), (mul_(d, b)))), m)))), m)), (mul_(a, c))));
	assert(eq_(temp_39_0, temp_39_1)) by {
		lemma_mod_mul_vanish(mul_(c, c), mul_(mul_(c, d), mul_(d, b)), m);
		cong_add_(mod_(mul_(c, c), m), mul_(a, c), mod_(sub_(mul_(c, c), mul_(mul_(mul_(c, d), mul_(d, b)), m)), m), mul_(a, c));
		lemma_eq_ref(mul_(a, c));
	}
	let temp_40_0 = (mul_((sub_(d, d)), (mul_(b, c))));
	let temp_40_1 = (mul_((mul_((sub_(d, d)), b)), c));
	assert(eq_(temp_40_0, temp_40_1)) by {
		lemma_mul_assoc(sub_(d, d), b, c);
	}
	let temp_41_0 = (mod_((add_((mod_((add_(b, c)), m)), (mod_((sub_(b, b)), m)))), m));
	let temp_41_1 = (mod_((add_((mod_((sub_(b, b)), m)), (mod_((add_(b, c)), m)))), m));
	assert(eq_(temp_41_0, temp_41_1)) by {
		lemma_add_comm(mod_(add_(b, c), m), mod_(sub_(b, b), m));
		cong_mod_(add_(mod_(add_(b, c), m), mod_(sub_(b, b), m)), m, add_(mod_(sub_(b, b), m), mod_(add_(b, c), m)), m);
		lemma_eq_ref(m);
	}
	let temp_42_0 = (mul_((add_(d, c)), (mul_(a, (mod_(b, m))))));
	let temp_42_1 = (mul_((mul_((add_(d, c)), a)), (mod_(b, m))));
	assert(eq_(temp_42_0, temp_42_1)) by {
		lemma_mul_assoc(add_(d, c), a, mod_(b, m));
	}
	let temp_43_0 = (mul_((mul_(as_elem(5), d)), (mod_((mul_(b, c)), m))));
	let temp_43_1 = (mul_((mul_(as_elem(5), d)), (mod_((mul_(c, b)), m))));
	assert(eq_(temp_43_0, temp_43_1)) by {
		lemma_mul_comm(b, c);
		cong_mul_(mul_(as_elem(5), d), mod_(mul_(b, c), m), mul_(as_elem(5), d), mod_(mul_(c, b), m));
		lemma_eq_ref(mul_(as_elem(5), d));
		cong_mod_(mul_(b, c), m, mul_(c, b), m);
		lemma_eq_ref(m);
	}
	let temp_44_0 = (sub_((sub_(d, b)), (mul_(a, a))));
	let temp_44_1 = (sub_((sub_(d, b)), (mul_(a, a))));
	assert(eq_(temp_44_0, temp_44_1)) by {
		lemma_eq_ref(temp_44_0);
	}
	let temp_45_0 = (mod_((mul_((mul_((mod_(c, m)), b)), (mul_((mod_(d, m)), c)))), m));
	let temp_45_1 = (mod_((mul_((mul_((mod_(c, m)), b)), (mul_(c, (mod_(d, m)))))), m));
	assert(eq_(temp_45_0, temp_45_1)) by {
		lemma_mul_comm(mod_(d, m), c);
		cong_mod_(mul_(mul_(mod_(c, m), b), mul_(mod_(d, m), c)), m, mul_(mul_(mod_(c, m), b), mul_(c, mod_(d, m))), m);
		lemma_eq_ref(m);
		lemma_eq_ref(mul_(mod_(c, m), b));
		cong_mul_(mul_(mod_(c, m), b), mul_(mod_(d, m), c), mul_(mod_(c, m), b), mul_(c, mod_(d, m)));
	}
	let temp_46_0 = (mul_((mul_(as_elem(4), (mod_(a, m)))), (mul_((mod_(a, m)), c))));
	let temp_46_1 = (mul_((mul_((mod_(a, m)), as_elem(4))), (mul_((mod_(a, m)), c))));
	assert(eq_(temp_46_0, temp_46_1)) by {
		lemma_mul_comm(as_elem(4), mod_(a, m));
		cong_mul_(mul_(as_elem(4), mod_(a, m)), mul_(mod_(a, m), c), mul_(mod_(a, m), as_elem(4)), mul_(mod_(a, m), c));
		lemma_eq_ref(mul_(mod_(a, m), c));
	}
	let temp_47_0 = (mul_((sub_(a, d)), (mul_(a, c))));
	let temp_47_1 = (mul_((mul_(a, c)), (sub_(a, d))));
	assert(eq_(temp_47_0, temp_47_1)) by {
		lemma_mul_comm(sub_(a, d), mul_(a, c));
	}
	let temp_48_0 = (mod_((mul_((add_(a, c)), (mul_(a, b)))), m));
	let temp_48_1 = (mod_((mul_((mul_((add_(a, c)), a)), b)), m));
	assert(eq_(temp_48_0, temp_48_1)) by {
		lemma_mul_assoc(add_(a, c), a, b);
		cong_mod_(mul_(add_(a, c), mul_(a, b)), m, mul_(mul_(add_(a, c), a), b), m);
		lemma_eq_ref(m);
	}
	let temp_49_0 = (mul_((mul_(d, b)), (mul_(d, b))));
	let temp_49_1 = (mul_((mul_(d, b)), (mul_(d, b))));
	assert(eq_(temp_49_0, temp_49_1)) by {
		lemma_eq_ref(temp_49_0);
	}
	let temp_50_0 = (mul_((sub_(b, a)), (mul_(b, c))));
	let temp_50_1 = (mul_((sub_(b, a)), (mul_(c, b))));
	assert(eq_(temp_50_0, temp_50_1)) by {
		cong_mul_(sub_(b, a), mul_(b, c), sub_(b, a), mul_(c, b));
		lemma_mul_comm(b, c);
		lemma_eq_ref(sub_(b, a));
	}
	let temp_51_0 = (mul_((mul_(d, d)), (sub_(a, d))));
	let temp_51_1 = (mul_(d, (mul_(d, (sub_(a, d))))));
	assert(eq_(temp_51_0, temp_51_1)) by {
		lemma_eq_sym(temp_51_1, temp_51_0);
		lemma_mul_assoc(d, d, sub_(a, d));
	}
	let temp_52_0 = (mul_((mul_(b, b)), (mul_((mod_(a, m)), c))));
	let temp_52_1 = (mul_((mul_(b, b)), (mul_((mod_((add_((mul_((add_((mod_((mul_((mod_(b, m)), b)), m)), (add_(c, d)))), m)), a)), m)), c))));
	assert(eq_(temp_52_0, temp_52_1)) by {
		lemma_mul_comm(b, b);
		lemma_mod_mul_vanish(a, add_(mod_(mul_(mod_(b, m), b), m), add_(c, d)), m);
		cong_mul_(mul_(b, b), mul_(mod_(a, m), c), mul_(b, b), mul_(mod_(add_(mul_(add_(mod_(mul_(mod_(b, m), b), m), add_(c, d)), m), a), m), c));
		cong_mul_(mod_(a, m), c, mod_(add_(mul_(add_(mod_(mul_(mod_(b, m), b), m), add_(c, d)), m), a), m), c);
		lemma_eq_ref(c);
	}
	let temp_53_0 = (mod_((mul_((mod_((mul_(c, b)), m)), (mul_(d, d)))), m));
	let temp_53_1 = (mod_((mul_((mul_((mod_((mul_(c, b)), m)), d)), d)), m));
	assert(eq_(temp_53_0, temp_53_1)) by {
		lemma_mul_assoc(mod_(mul_(c, b), m), d, d);
		cong_mod_(mul_(mod_(mul_(c, b), m), mul_(d, d)), m, mul_(mul_(mod_(mul_(c, b), m), d), d), m);
		lemma_eq_ref(m);
	}
	let temp_54_0 = (mul_((sub_(a, d)), d));
	let temp_54_1 = (mul_(d, (sub_(a, d))));
	assert(eq_(temp_54_0, temp_54_1)) by {
		lemma_mul_comm(sub_(a, d), d);
	}
	let temp_55_0 = (mul_((mul_(b, a)), (add_(d, a))));
	let temp_55_1 = (add_((mul_((mul_(b, a)), d)), (mul_((mul_(b, a)), a))));
	assert(eq_(temp_55_0, temp_55_1)) by {
		lemma_mul_dist(mul_(b, a), d, a);
	}
	let temp_56_0 = (sub_((mod_((mul_((mod_(d, m)), (mod_(b, m)))), m)), (mul_(d, a))));
	let temp_56_1 = (sub_((mod_((mul_((mod_(b, m)), (mod_(d, m)))), m)), (mul_(d, a))));
	assert(eq_(temp_56_0, temp_56_1)) by {
		lemma_mul_comm(mod_(d, m), mod_(b, m));
		lemma_mul_comm(d, a);
		lemma_mul_comm(a, d);
		cong_sub_(mod_(mul_(mod_(d, m), mod_(b, m)), m), mul_(d, a), mod_(mul_(mod_(b, m), mod_(d, m)), m), mul_(d, a));
		lemma_eq_ref(m);
		lemma_eq_trans(mul_(d, a), mul_(a, d), mul_(d, a));
		cong_mod_(mul_(mod_(d, m), mod_(b, m)), m, mul_(mod_(b, m), mod_(d, m)), m);
	}
	let temp_57_0 = (mul_((mul_(a, b)), (mul_(b, as_elem(64)))));
	let temp_57_1 = (mul_(a, (mul_(b, (mul_(b, as_elem(64)))))));
	assert(eq_(temp_57_0, temp_57_1)) by {
		lemma_eq_sym(temp_57_1, temp_57_0);
		lemma_mul_assoc(a, b, mul_(b, as_elem(64)));
	}
	let temp_58_0 = (mul_((mul_(b, b)), (mod_((mul_(c, d)), m))));
	let temp_58_1 = (mul_(b, (mul_(b, (mod_((mul_(c, d)), m))))));
	assert(eq_(temp_58_0, temp_58_1)) by {
		lemma_mul_assoc(b, b, mod_(mul_(c, d), m));
		lemma_eq_sym(temp_58_1, temp_58_0);
	}
	let temp_59_0 = (add_((mul_(a, a)), (mul_(b, c))));
	let temp_59_1 = (add_((mul_(b, c)), (mul_(a, a))));
	assert(eq_(temp_59_0, temp_59_1)) by {
		lemma_add_comm(mul_(a, a), mul_(b, c));
	}
	let temp_60_0 = (mul_((mul_(a, d)), (mul_(a, c))));
	let temp_60_1 = (mul_(a, (mul_(d, (mul_(a, c))))));
	assert(eq_(temp_60_0, temp_60_1)) by {
		lemma_eq_sym(temp_60_1, temp_60_0);
		lemma_mul_assoc(a, d, mul_(a, c));
	}
	let temp_61_0 = (mul_((mul_((mod_(d, m)), a)), (mod_((mul_((mod_(a, m)), a)), m))));
	let temp_61_1 = (mul_((mod_((mul_((mod_(a, m)), a)), m)), (mul_((mod_(d, m)), a))));
	assert(eq_(temp_61_0, temp_61_1)) by {
		lemma_mul_comm(mul_(mod_(d, m), a), mod_(mul_(mod_(a, m), a), m));
	}
	let temp_62_0 = (mul_((mul_(a, d)), (mul_((mod_(d, m)), a))));
	let temp_62_1 = (mul_((mul_(a, d)), (mul_((mod_((add_(d, (mul_((mul_((sub_(a, c)), (mul_(a, a)))), m)))), m)), a))));
	assert(eq_(temp_62_0, temp_62_1)) by {
		lemma_eq_ref(mul_(a, d));
		lemma_mod_mul_vanish(d, mul_(sub_(a, c), mul_(a, a)), m);
		cong_mul_(mul_(a, d), mul_(mod_(d, m), a), mul_(a, d), mul_(mod_(add_(d, mul_(mul_(sub_(a, c), mul_(a, a)), m)), m), a));
		lemma_eq_ref(a);
		cong_mul_(mod_(d, m), a, mod_(add_(d, mul_(mul_(sub_(a, c), mul_(a, a)), m)), m), a);
	}
	let temp_63_0 = (add_((mul_(d, d)), (mul_(d, a))));
	let temp_63_1 = (add_((mul_(d, a)), (mul_(d, d))));
	assert(eq_(temp_63_0, temp_63_1)) by {
		lemma_add_comm(mul_(d, d), mul_(d, a));
	}
	let temp_64_0 = (mul_((add_(a, c)), (mul_(b, as_elem(61)))));
	let temp_64_1 = (mul_((mul_((add_(a, c)), b)), as_elem(61)));
	assert(eq_(temp_64_0, temp_64_1)) by {
		lemma_mul_assoc(add_(a, c), b, as_elem(61));
	}
	let temp_65_0 = (mul_((mul_(as_elem(87), a)), (mul_(a, a))));
	let temp_65_1 = (mul_((mul_((mul_(as_elem(87), a)), a)), a));
	assert(eq_(temp_65_0, temp_65_1)) by {
		lemma_mul_assoc(mul_(as_elem(87), a), a, a);
	}
	let temp_66_0 = (mul_((sub_(b, d)), (mul_(d, (mod_(a, m))))));
	let temp_66_1 = (sub_((mul_(b, (mul_(d, (mod_(a, m)))))), (mul_(d, (mul_(d, (mod_(a, m))))))));
	assert(eq_(temp_66_0, temp_66_1)) by {
		lemma_mul_dist(mul_(d, mod_(a, m)), b, d);
	}
	let temp_67_0 = (sub_((add_((mod_(d, m)), c)), (add_(d, (mod_(a, m))))));
	let temp_67_1 = (sub_((add_((mod_((sub_(d, (mul_((mod_((sub_((mul_(a, a)), (mul_(d, c)))), m)), m)))), m)), c)), (add_(d, (mod_(a, m))))));
	assert(eq_(temp_67_0, temp_67_1)) by {
		lemma_mod_mul_vanish(d, mod_(sub_(mul_(a, a), mul_(d, c)), m), m);
		cong_sub_(add_(mod_(d, m), c), add_(d, mod_(a, m)), add_(mod_(sub_(d, mul_(mod_(sub_(mul_(a, a), mul_(d, c)), m), m)), m), c), add_(d, mod_(a, m)));
		lemma_eq_ref(c);
		cong_add_(mod_(d, m), c, mod_(sub_(d, mul_(mod_(sub_(mul_(a, a), mul_(d, c)), m), m)), m), c);
		lemma_eq_ref(add_(d, mod_(a, m)));
	}
	let temp_68_0 = (add_((sub_(c, b)), (mul_(b, c))));
	let temp_68_1 = (add_((mul_(b, c)), (sub_(c, b))));
	assert(eq_(temp_68_0, temp_68_1)) by {
		lemma_add_comm(sub_(c, b), mul_(b, c));
	}
	let temp_69_0 = (mul_((mul_((mod_(b, m)), a)), (mul_(c, c))));
	let temp_69_1 = (mul_((mul_(c, c)), (mul_((mod_(b, m)), a))));
	assert(eq_(temp_69_0, temp_69_1)) by {
		lemma_mul_comm(mul_(mod_(b, m), a), mul_(c, c));
	}
	let temp_70_0 = (mul_((mul_(c, (mod_(a, m)))), (mod_((mul_(d, a)), m))));
	let temp_70_1 = (mul_(c, (mul_((mod_(a, m)), (mod_((mul_(d, a)), m))))));
	assert(eq_(temp_70_0, temp_70_1)) by {
		lemma_mul_assoc(c, mod_(a, m), mod_(mul_(d, a), m));
		lemma_eq_sym(temp_70_1, temp_70_0);
	}
	let temp_71_0 = (mul_((mul_(b, c)), (mul_(c, c))));
	let temp_71_1 = (mul_((mul_((mul_(b, c)), c)), c));
	assert(eq_(temp_71_0, temp_71_1)) by {
		lemma_mul_assoc(mul_(b, c), c, c);
	}
	let temp_72_0 = (mul_((mul_(a, a)), (mul_(a, a))));
	let temp_72_1 = (mul_((mul_(a, a)), (mul_(a, a))));
	assert(eq_(temp_72_0, temp_72_1)) by {
		lemma_eq_ref(temp_72_0);
	}
	let temp_73_0 = (sub_((mul_((mod_(c, m)), b)), (add_(c, d))));
	let temp_73_1 = (sub_((mul_((mod_(c, m)), b)), (add_(d, c))));
	assert(eq_(temp_73_0, temp_73_1)) by {
		lemma_add_comm(c, d);
		cong_sub_(mul_(mod_(c, m), b), add_(c, d), mul_(mod_(c, m), b), add_(d, c));
		lemma_eq_ref(mul_(mod_(c, m), b));
	}
	let temp_74_0 = (mod_((mul_((add_(d, a)), (mul_(b, c)))), m));
	let temp_74_1 = (mod_((add_((mul_(d, (mul_(b, c)))), (mul_(a, (mul_(b, c)))))), m));
	assert(eq_(temp_74_0, temp_74_1)) by {
		lemma_mul_dist(d, a, mul_(b, c));
		cong_mod_(mul_(add_(d, a), mul_(b, c)), m, add_(mul_(d, mul_(b, c)), mul_(a, mul_(b, c))), m);
		lemma_eq_ref(m);
	}
	let temp_75_0 = (mul_((mul_(b, a)), (mul_(b, a))));
	let temp_75_1 = (mul_((mul_(b, a)), (mul_(b, a))));
	assert(eq_(temp_75_0, temp_75_1)) by {
		lemma_eq_ref(temp_75_0);
	}
	let temp_76_0 = (mul_((mul_(c, c)), (mul_(a, d))));
	let temp_76_1 = (mul_(c, (mul_(c, (mul_(a, d))))));
	assert(eq_(temp_76_0, temp_76_1)) by {
		lemma_eq_sym(temp_76_1, temp_76_0);
		lemma_mul_assoc(c, c, mul_(a, d));
	}
	let temp_77_0 = (mul_((mul_(b, d)), (sub_(d, b))));
	let temp_77_1 = (mul_(b, (mul_(d, (sub_(d, b))))));
	assert(eq_(temp_77_0, temp_77_1)) by {
		lemma_eq_sym(temp_77_1, temp_77_0);
		lemma_mul_assoc(b, d, sub_(d, b));
	}
	let temp_78_0 = (mul_((mul_(d, a)), (mul_(c, a))));
	let temp_78_1 = (mul_((mul_(c, a)), (mul_(d, a))));
	assert(eq_(temp_78_0, temp_78_1)) by {
		lemma_mul_comm(mul_(d, a), mul_(c, a));
	}
	let temp_79_0 = (add_((sub_(a, a)), (mul_(a, a))));
	let temp_79_1 = (add_((mul_(a, a)), (sub_(a, a))));
	assert(eq_(temp_79_0, temp_79_1)) by {
		lemma_add_comm(sub_(a, a), mul_(a, a));
	}
	let temp_80_0 = (mod_((mul_((mod_((mul_(c, b)), m)), (add_((mod_(b, m)), a)))), m));
	let temp_80_1 = (mod_((mul_((add_((mod_(b, m)), a)), (mod_((mul_(c, b)), m)))), m));
	assert(eq_(temp_80_0, temp_80_1)) by {
		lemma_mul_comm(mod_(mul_(c, b), m), add_(mod_(b, m), a));
		cong_mod_(mul_(mod_(mul_(c, b), m), add_(mod_(b, m), a)), m, mul_(add_(mod_(b, m), a), mod_(mul_(c, b), m)), m);
		lemma_eq_ref(m);
	}
	let temp_81_0 = (sub_((mul_(c, d)), (mul_(d, c))));
	let temp_81_1 = (sub_((mul_(c, d)), (mul_(c, d))));
	assert(eq_(temp_81_0, temp_81_1)) by {
		cong_sub_(mul_(c, d), mul_(d, c), mul_(c, d), mul_(c, d));
		lemma_mul_comm(d, c);
		lemma_eq_ref(mul_(c, d));
	}
	let temp_82_0 = (add_((add_(a, a)), (mul_(b, c))));
	let temp_82_1 = (add_((add_(a, a)), (mul_(c, b))));
	assert(eq_(temp_82_0, temp_82_1)) by {
		cong_add_(add_(a, a), mul_(b, c), add_(a, a), mul_(c, b));
		lemma_add_comm(a, a);
		lemma_mul_comm(b, c);
	}
	let temp_83_0 = (mul_((mod_((add_(a, d)), m)), (add_(b, b))));
	let temp_83_1 = (mul_((mod_((add_((mod_(a, m)), (mod_(d, m)))), m)), (add_(b, b))));
	assert(eq_(temp_83_0, temp_83_1)) by {
		lemma_mod_add_noop(a, d, m);
		lemma_add_comm(b, b);
		cong_mul_(mod_(add_(a, d), m), add_(b, b), mod_(add_(mod_(a, m), mod_(d, m)), m), add_(b, b));
	}
	let temp_84_0 = (mul_((mul_(a, a)), (mul_(b, b))));
	let temp_84_1 = (mul_((mul_(a, a)), (mul_(b, b))));
	assert(eq_(temp_84_0, temp_84_1)) by {
		lemma_eq_ref(temp_84_0);
	}
	let temp_85_0 = (sub_((sub_(a, a)), (mul_(a, c))));
	let temp_85_1 = (sub_((sub_(a, a)), (mul_(c, a))));
	assert(eq_(temp_85_0, temp_85_1)) by {
		cong_sub_(sub_(a, a), mul_(a, c), sub_(a, a), mul_(c, a));
		lemma_mul_comm(a, c);
		cong_sub_(a, a, a, a);
		lemma_eq_ref(a);
	}
	let temp_86_0 = (mul_((add_(b, (mod_(as_elem(94), m)))), (mul_(d, c))));
	let temp_86_1 = (mul_((add_((mod_(as_elem(94), m)), b)), (mul_(d, c))));
	assert(eq_(temp_86_0, temp_86_1)) by {
		lemma_add_comm(b, mod_(as_elem(94), m));
		cong_mul_(add_(b, mod_(as_elem(94), m)), mul_(d, c), add_(mod_(as_elem(94), m), b), mul_(d, c));
		lemma_eq_ref(mul_(d, c));
	}
	let temp_87_0 = (mul_((sub_(b, (mod_(d, m)))), (mul_(c, a))));
	let temp_87_1 = (mul_((sub_(b, (mod_((sub_(d, (mul_((mul_((mul_((mod_(c, m)), a)), (mul_(as_elem(77), as_elem(85))))), m)))), m)))), (mul_(c, a))));
	assert(eq_(temp_87_0, temp_87_1)) by {
		cong_mul_(sub_(b, mod_(d, m)), mul_(c, a), sub_(b, mod_(sub_(d, mul_(mul_(mul_(mod_(c, m), a), mul_(as_elem(77), as_elem(85))), m)), m)), mul_(c, a));
		lemma_mod_mul_vanish(d, mul_(mul_(mod_(c, m), a), mul_(as_elem(77), as_elem(85))), m);
		cong_sub_(b, mod_(d, m), b, mod_(sub_(d, mul_(mul_(mul_(mod_(c, m), a), mul_(as_elem(77), as_elem(85))), m)), m));
		lemma_eq_ref(mul_(c, a));
		lemma_eq_ref(b);
	}
	let temp_88_0 = (mul_((mul_((mod_(c, m)), (mod_(c, m)))), (mul_((mod_(b, m)), (mod_(d, m))))));
	let temp_88_1 = (mul_((mul_((mod_(c, m)), (mod_(c, m)))), (mul_((mod_((sub_(b, (mul_((mul_((mul_(c, b)), (mul_(a, b)))), m)))), m)), (mod_(d, m))))));
	assert(eq_(temp_88_0, temp_88_1)) by {
		cong_mul_(mul_(mod_(c, m), mod_(c, m)), mul_(mod_(b, m), mod_(d, m)), mul_(mod_(c, m), mod_(c, m)), mul_(mod_(sub_(b, mul_(mul_(mul_(c, b), mul_(a, b)), m)), m), mod_(d, m)));
		lemma_mod_mul_vanish(b, mul_(mul_(c, b), mul_(a, b)), m);
		lemma_eq_ref(mul_(mod_(c, m), mod_(c, m)));
		lemma_eq_ref(mod_(d, m));
		cong_mul_(mod_(b, m), mod_(d, m), mod_(sub_(b, mul_(mul_(mul_(c, b), mul_(a, b)), m)), m), mod_(d, m));
	}
	let temp_89_0 = (mul_((mul_(b, d)), (mul_(a, a))));
	let temp_89_1 = (mul_(b, (mul_(d, (mul_(a, a))))));
	assert(eq_(temp_89_0, temp_89_1)) by {
		lemma_eq_sym(temp_89_1, temp_89_0);
		lemma_mul_assoc(b, d, mul_(a, a));
	}
	let temp_90_0 = (mul_((mul_(a, (mod_(d, m)))), (mul_(c, as_elem(71)))));
	let temp_90_1 = (mul_((mul_(a, (mod_((add_(d, (mul_((mul_((sub_(d, b)), (mul_((mod_(a, m)), d)))), m)))), m)))), (mul_(c, as_elem(71)))));
	assert(eq_(temp_90_0, temp_90_1)) by {
		lemma_mod_mul_vanish(d, mul_(sub_(d, b), mul_(mod_(a, m), d)), m);
		cong_mul_(mul_(a, mod_(d, m)), mul_(c, as_elem(71)), mul_(a, mod_(add_(d, mul_(mul_(sub_(d, b), mul_(mod_(a, m), d)), m)), m)), mul_(c, as_elem(71)));
		lemma_eq_ref(a);
		cong_mul_(a, mod_(d, m), a, mod_(add_(d, mul_(mul_(sub_(d, b), mul_(mod_(a, m), d)), m)), m));
		lemma_eq_ref(mul_(c, as_elem(71)));
	}
	let temp_91_0 = (mul_((mul_(d, c)), (mul_((mod_(b, m)), (mod_(d, m))))));
	let temp_91_1 = (mul_(d, (mul_(c, (mul_((mod_(b, m)), (mod_(d, m))))))));
	assert(eq_(temp_91_0, temp_91_1)) by {
		lemma_mul_assoc(d, c, mul_(mod_(b, m), mod_(d, m)));
		lemma_eq_sym(temp_91_1, temp_91_0);
	}
	let temp_92_0 = (mul_((mod_((mul_(b, a)), m)), (mul_(d, c))));
	let temp_92_1 = (mul_((mod_((sub_((mul_(b, a)), (mul_((mul_((mul_((mod_(a, m)), b)), (mod_((mul_(a, d)), m)))), m)))), m)), (mul_(d, c))));
	assert(eq_(temp_92_0, temp_92_1)) by {
		lemma_eq_ref(mul_(d, c));
		lemma_mod_mul_vanish(mul_(b, a), mul_(mul_(mod_(a, m), b), mod_(mul_(a, d), m)), m);
		cong_mul_(mod_(mul_(b, a), m), mul_(d, c), mod_(sub_(mul_(b, a), mul_(mul_(mul_(mod_(a, m), b), mod_(mul_(a, d), m)), m)), m), mul_(d, c));
	}

}

} // verus!