use builtin_macros::*;
// use builtin::*;
mod nl_basics;
use crate::nl_basics::*;
verus! {

pub proof fn free_0(a: Elem, b: Elem, c: Elem, d: Elem, m: Elem)
{
	let temp_0_0 = (mul_((mul_(d, c)), (mul_(c, (mod_(d, m))))));
	let temp_0_1 = (mul_((mul_(c, (mod_(d, m)))), (mul_(d, c))));
	assert(eq_(temp_0_0, temp_0_1)) by {
		lemma_mul_comm(mul_(d, c), mul_(c, mod_(d, m)));
	}
	let temp_1_0 = (mul_((mul_(a, d)), (add_(b, a))));
	let temp_1_1 = (mul_(a, (mul_(d, (add_(b, a))))));
	assert(eq_(temp_1_0, temp_1_1)) by {
		lemma_eq_sym(temp_1_1, temp_1_0);
		lemma_mul_assoc(a, d, add_(b, a));
	}
	let temp_2_0 = (sub_((add_(b, (mod_(d, m)))), (mod_((sub_(b, c)), m))));
	let temp_2_1 = (sub_((add_(b, (mod_((sub_(d, (mul_((mul_((add_(a, d)), (mul_(c, d)))), m)))), m)))), (mod_((sub_(b, c)), m))));
	assert(eq_(temp_2_0, temp_2_1)) by {
		lemma_mod_mul_vanish(d, mul_(add_(a, d), mul_(c, d)), m);
		cong_sub_(add_(b, mod_(d, m)), mod_(sub_(b, c), m), add_(b, mod_(sub_(d, mul_(mul_(add_(a, d), mul_(c, d)), m)), m)), mod_(sub_(b, c), m));
		lemma_eq_ref(b);
		cong_add_(b, mod_(d, m), b, mod_(sub_(d, mul_(mul_(add_(a, d), mul_(c, d)), m)), m));
		lemma_eq_ref(mod_(sub_(b, c), m));
	}
	let temp_3_0 = (mul_((mul_(a, a)), (mod_((mul_(b, (mod_(d, m)))), m))));
	let temp_3_1 = (mul_(a, (mul_(a, (mod_((mul_(b, (mod_(d, m)))), m))))));
	assert(eq_(temp_3_0, temp_3_1)) by {
		lemma_mul_assoc(a, a, mod_(mul_(b, mod_(d, m)), m));
		lemma_eq_sym(temp_3_1, temp_3_0);
	}
	let temp_4_0 = (mul_((mul_(c, a)), (mul_(c, b))));
	let temp_4_1 = (mul_((mul_(a, c)), (mul_(c, b))));
	assert(eq_(temp_4_0, temp_4_1)) by {
		cong_mul_(mul_(c, a), mul_(c, b), mul_(a, c), mul_(c, b));
		lemma_mul_comm(c, a);
		lemma_eq_ref(mul_(c, b));
	}
	let temp_5_0 = (mul_((mul_(b, d)), (mul_(b, d))));
	let temp_5_1 = (mul_(b, (mul_(d, (mul_(b, d))))));
	assert(eq_(temp_5_0, temp_5_1)) by {
		lemma_eq_sym(temp_5_1, temp_5_0);
		lemma_mul_assoc(b, d, mul_(b, d));
	}
	let temp_6_0 = (mul_((mul_(d, a)), (sub_(b, c))));
	let temp_6_1 = (mul_(d, (mul_(a, (sub_(b, c))))));
	assert(eq_(temp_6_0, temp_6_1)) by {
		lemma_eq_sym(temp_6_1, temp_6_0);
		lemma_mul_assoc(d, a, sub_(b, c));
	}
	let temp_7_0 = (mul_((mod_((mul_((mod_(d, m)), d)), m)), (mul_(b, b))));
	let temp_7_1 = (mul_((mod_((mul_((mod_(d, m)), d)), m)), (mul_(b, b))));
	assert(eq_(temp_7_0, temp_7_1)) by {
		lemma_eq_ref(temp_7_0);
	}
	let temp_8_0 = (mod_((add_((sub_(a, c)), (mul_(c, c)))), m));
	let temp_8_1 = (mod_((add_((sub_(a, c)), (mul_(c, c)))), m));
	assert(eq_(temp_8_0, temp_8_1)) by {
		lemma_eq_ref(temp_8_0);
	}
	let temp_9_0 = (mul_((mod_((mul_((mod_(b, m)), d)), m)), (add_(a, d))));
	let temp_9_1 = (mul_((add_(a, d)), (mod_((mul_((mod_(b, m)), d)), m))));
	assert(eq_(temp_9_0, temp_9_1)) by {
		lemma_mul_comm(mod_(mul_(mod_(b, m), d), m), add_(a, d));
	}
	let temp_10_0 = (mul_((sub_(c, a)), (mul_((mod_(c, m)), (mod_(a, m))))));
	let temp_10_1 = (mul_((mul_((mod_(c, m)), (mod_(a, m)))), (sub_(c, a))));
	assert(eq_(temp_10_0, temp_10_1)) by {
		lemma_mul_comm(sub_(c, a), mul_(mod_(c, m), mod_(a, m)));
	}
	let temp_11_0 = (sub_((mul_(d, d)), (sub_(b, a))));
	let temp_11_1 = (sub_((mul_(d, d)), (sub_(b, a))));
	assert(eq_(temp_11_0, temp_11_1)) by {
		lemma_eq_ref(temp_11_0);
	}
	let temp_12_0 = (mul_((mod_((mul_(c, d)), m)), (mul_(d, b))));
	let temp_12_1 = (mul_((mod_((add_((mul_((mul_((mul_(d, a)), (mul_(d, d)))), m)), (mul_(c, d)))), m)), (mul_(d, b))));
	assert(eq_(temp_12_0, temp_12_1)) by {
		lemma_mod_mul_vanish(mul_(c, d), mul_(mul_(d, a), mul_(d, d)), m);
		cong_mul_(mod_(mul_(c, d), m), mul_(d, b), mod_(add_(mul_(mul_(mul_(d, a), mul_(d, d)), m), mul_(c, d)), m), mul_(d, b));
		lemma_eq_ref(mul_(d, b));
	}
	let temp_13_0 = (mul_((mul_(a, d)), (mul_(a, b))));
	let temp_13_1 = (mul_(a, (mul_(d, (mul_(a, b))))));
	assert(eq_(temp_13_0, temp_13_1)) by {
		lemma_eq_sym(temp_13_1, temp_13_0);
		lemma_mul_assoc(a, d, mul_(a, b));
	}
	let temp_14_0 = (mul_((mul_((mod_(d, m)), c)), (sub_(a, c))));
	let temp_14_1 = (mul_((mul_(c, (mod_(d, m)))), (sub_(a, c))));
	assert(eq_(temp_14_0, temp_14_1)) by {
		lemma_mul_comm(mod_(d, m), c);
		cong_mul_(mul_(mod_(d, m), c), sub_(a, c), mul_(c, mod_(d, m)), sub_(a, c));
		lemma_eq_ref(sub_(a, c));
	}
	let temp_15_0 = (mul_((mul_(d, c)), (mul_(c, c))));
	let temp_15_1 = (mul_((mul_(c, d)), (mul_(c, c))));
	assert(eq_(temp_15_0, temp_15_1)) by {
		cong_mul_(mul_(d, c), mul_(c, c), mul_(c, d), mul_(c, c));
		lemma_mul_comm(d, c);
		lemma_mul_comm(c, c);
	}
	let temp_16_0 = (mul_((mul_(c, b)), (mul_(a, d))));
	let temp_16_1 = (mul_((mul_(a, d)), (mul_(c, b))));
	assert(eq_(temp_16_0, temp_16_1)) by {
		lemma_mul_comm(mul_(c, b), mul_(a, d));
	}
	let temp_17_0 = (add_((mul_(c, c)), c));
	let temp_17_1 = (add_((mul_(c, c)), c));
	assert(eq_(temp_17_0, temp_17_1)) by {
		lemma_eq_ref(temp_17_0);
	}
	let temp_18_0 = (mul_((add_(b, d)), (mul_(b, b))));
	let temp_18_1 = (add_((mul_(b, (mul_(b, b)))), (mul_(d, (mul_(b, b))))));
	assert(eq_(temp_18_0, temp_18_1)) by {
		lemma_mul_dist(b, d, mul_(b, b));
	}
	let temp_19_0 = (mul_((sub_(d, (mod_(b, m)))), (mul_(a, c))));
	let temp_19_1 = (mul_((mul_(a, c)), (sub_(d, (mod_(b, m))))));
	assert(eq_(temp_19_0, temp_19_1)) by {
		lemma_mul_comm(sub_(d, mod_(b, m)), mul_(a, c));
	}
	let temp_20_0 = (mul_((add_(a, (mod_(b, m)))), c));
	let temp_20_1 = (mul_((add_((mod_(b, m)), a)), c));
	assert(eq_(temp_20_0, temp_20_1)) by {
		lemma_add_comm(a, mod_(b, m));
		cong_mul_(add_(a, mod_(b, m)), c, add_(mod_(b, m), a), c);
		lemma_eq_ref(c);
	}
	let temp_21_0 = (mul_((mul_(a, b)), (mul_(b, c))));
	let temp_21_1 = (mul_(a, (mul_(b, (mul_(b, c))))));
	assert(eq_(temp_21_0, temp_21_1)) by {
		lemma_eq_sym(temp_21_1, temp_21_0);
		lemma_mul_assoc(a, b, mul_(b, c));
	}
	let temp_22_0 = (mul_(b, (mul_((mod_(d, m)), c))));
	let temp_22_1 = (mul_(b, (mul_((mod_((add_((mul_((mul_((mul_(b, b)), (mul_(d, c)))), m)), d)), m)), c))));
	assert(eq_(temp_22_0, temp_22_1)) by {
		lemma_mod_mul_vanish(d, mul_(mul_(b, b), mul_(d, c)), m);
		cong_mul_(b, mul_(mod_(d, m), c), b, mul_(mod_(add_(mul_(mul_(mul_(b, b), mul_(d, c)), m), d), m), c));
		lemma_eq_ref(b);
		cong_mul_(mod_(d, m), c, mod_(add_(mul_(mul_(mul_(b, b), mul_(d, c)), m), d), m), c);
		lemma_eq_ref(c);
	}
	let temp_23_0 = (sub_((add_(c, a)), (mul_((mod_(b, m)), d))));
	let temp_23_1 = (sub_((add_(c, a)), (mul_(d, (mod_(b, m))))));
	assert(eq_(temp_23_0, temp_23_1)) by {
		lemma_mul_comm(mod_(b, m), d);
		cong_sub_(add_(c, a), mul_(mod_(b, m), d), add_(c, a), mul_(d, mod_(b, m)));
		lemma_eq_ref(add_(c, a));
	}
	let temp_24_0 = (mod_((mul_((add_(a, as_elem(95))), (mul_(b, d)))), m));
	let temp_24_1 = (mod_((mul_((add_(as_elem(95), a)), (mul_(b, d)))), m));
	assert(eq_(temp_24_0, temp_24_1)) by {
		lemma_add_comm(a, as_elem(95));
		cong_mod_(mul_(add_(a, as_elem(95)), mul_(b, d)), m, mul_(add_(as_elem(95), a), mul_(b, d)), m);
		lemma_eq_ref(mul_(b, d));
		cong_mul_(add_(a, as_elem(95)), mul_(b, d), add_(as_elem(95), a), mul_(b, d));
		lemma_eq_ref(m);
	}
	let temp_25_0 = (mul_((mul_(c, b)), (mod_((mul_(a, a)), m))));
	let temp_25_1 = (mul_((mod_((mul_(a, a)), m)), (mul_(c, b))));
	assert(eq_(temp_25_0, temp_25_1)) by {
		lemma_mul_comm(mul_(c, b), mod_(mul_(a, a), m));
	}
	let temp_26_0 = (mod_((mul_((mul_(c, as_elem(22))), (mod_((mul_(a, (mod_(b, m)))), m)))), m));
	let temp_26_1 = (mod_((mod_((mul_((mul_(a, (mod_(b, m)))), (mul_(c, as_elem(22))))), m)), m));
	assert(eq_(temp_26_0, temp_26_1)) by {
		lemma_mod_mul_noop(mul_(a, mod_(b, m)), mul_(c, as_elem(22)), m);
		lemma_eq_sym(temp_26_1, temp_26_0);
	}
	let temp_27_0 = (mul_((mul_(c, b)), (mul_(c, c))));
	let temp_27_1 = (mul_((mul_((mul_(c, b)), c)), c));
	assert(eq_(temp_27_0, temp_27_1)) by {
		lemma_mul_assoc(mul_(c, b), c, c);
	}
	let temp_28_0 = (mul_((mul_(c, a)), (sub_((mod_(c, m)), d))));
	let temp_28_1 = (mul_((sub_((mod_(c, m)), d)), (mul_(c, a))));
	assert(eq_(temp_28_0, temp_28_1)) by {
		lemma_mul_comm(mul_(c, a), sub_(mod_(c, m), d));
	}
	let temp_29_0 = (mul_((mul_(b, b)), (mul_(c, d))));
	let temp_29_1 = (mul_((mul_((mul_(b, b)), c)), d));
	assert(eq_(temp_29_0, temp_29_1)) by {
		lemma_mul_assoc(mul_(b, b), c, d);
	}
	let temp_30_0 = (mul_((mul_(c, c)), (mod_((add_(c, b)), m))));
	let temp_30_1 = (mul_((mul_(c, c)), (mod_((add_(b, c)), m))));
	assert(eq_(temp_30_0, temp_30_1)) by {
		lemma_mul_comm(c, c);
		lemma_add_comm(c, b);
		cong_mul_(mul_(c, c), mod_(add_(c, b), m), mul_(c, c), mod_(add_(b, c), m));
		lemma_eq_ref(m);
		cong_mod_(add_(c, b), m, add_(b, c), m);
	}
	let temp_31_0 = (mul_((mul_(d, d)), (mul_(d, c))));
	let temp_31_1 = (mul_((mul_(d, d)), (mul_(c, d))));
	assert(eq_(temp_31_0, temp_31_1)) by {
		cong_mul_(mul_(d, d), mul_(d, c), mul_(d, d), mul_(c, d));
		lemma_mul_comm(d, d);
		lemma_mul_comm(d, c);
	}
	let temp_32_0 = (mul_((mul_(b, d)), (mul_(a, c))));
	let temp_32_1 = (mul_((mul_((mul_(b, d)), a)), c));
	assert(eq_(temp_32_0, temp_32_1)) by {
		lemma_mul_assoc(mul_(b, d), a, c);
	}
	let temp_33_0 = (mul_((mod_((mul_(a, c)), m)), (mul_(a, a))));
	let temp_33_1 = (mul_((mod_((mul_(c, a)), m)), (mul_(a, a))));
	assert(eq_(temp_33_0, temp_33_1)) by {
		lemma_mul_comm(a, c);
		lemma_mul_comm(a, a);
		cong_mul_(mod_(mul_(a, c), m), mul_(a, a), mod_(mul_(c, a), m), mul_(a, a));
		cong_mod_(mul_(a, c), m, mul_(c, a), m);
		lemma_eq_ref(m);
	}
	let temp_34_0 = (mul_((mul_(a, d)), (sub_(a, (mod_(b, m))))));
	let temp_34_1 = (mul_(a, (mul_(d, (sub_(a, (mod_(b, m))))))));
	assert(eq_(temp_34_0, temp_34_1)) by {
		lemma_mul_assoc(a, d, sub_(a, mod_(b, m)));
		lemma_eq_sym(temp_34_1, temp_34_0);
	}
	let temp_35_0 = (mul_((mul_(d, a)), (add_(a, d))));
	let temp_35_1 = (add_((mul_((mul_(d, a)), a)), (mul_((mul_(d, a)), d))));
	assert(eq_(temp_35_0, temp_35_1)) by {
		lemma_mul_dist(mul_(d, a), a, d);
	}
	let temp_36_0 = (mul_((mod_((add_(c, d)), m)), (mul_(a, d))));
	let temp_36_1 = (mul_((mod_((add_((mod_(c, m)), d)), m)), (mul_(a, d))));
	assert(eq_(temp_36_0, temp_36_1)) by {
		lemma_mod_add_noop(c, d, m);
		cong_mul_(mod_(add_(c, d), m), mul_(a, d), mod_(add_(mod_(c, m), d), m), mul_(a, d));
		lemma_eq_ref(mul_(a, d));
	}
	let temp_37_0 = (mul_((mul_(c, c)), (mul_((mod_(a, m)), c))));
	let temp_37_1 = (mul_((mul_(c, c)), (mul_((mod_((add_((mul_((mul_((mul_(b, b)), (mul_(c, c)))), m)), a)), m)), c))));
	assert(eq_(temp_37_0, temp_37_1)) by {
		lemma_mul_comm(c, c);
		lemma_mod_mul_vanish(a, mul_(mul_(b, b), mul_(c, c)), m);
		cong_mul_(mul_(c, c), mul_(mod_(a, m), c), mul_(c, c), mul_(mod_(add_(mul_(mul_(mul_(b, b), mul_(c, c)), m), a), m), c));
		lemma_eq_ref(c);
		cong_mul_(mod_(a, m), c, mod_(add_(mul_(mul_(mul_(b, b), mul_(c, c)), m), a), m), c);
	}
	let temp_38_0 = (mul_((mul_(d, b)), (mul_(c, c))));
	let temp_38_1 = (mul_((mul_((mul_(d, b)), c)), c));
	assert(eq_(temp_38_0, temp_38_1)) by {
		lemma_mul_assoc(mul_(d, b), c, c);
	}
	let temp_39_0 = (mul_((mul_(d, a)), (mul_(d, d))));
	let temp_39_1 = (mul_((mul_(d, a)), (mul_(d, d))));
	assert(eq_(temp_39_0, temp_39_1)) by {
		lemma_eq_ref(temp_39_0);
	}
	let temp_40_0 = (mul_((mul_(c, a)), (add_(d, b))));
	let temp_40_1 = (mul_(c, (mul_(a, (add_(d, b))))));
	assert(eq_(temp_40_0, temp_40_1)) by {
		lemma_eq_sym(temp_40_1, temp_40_0);
		lemma_mul_assoc(c, a, add_(d, b));
	}
	let temp_41_0 = (mul_((mul_(d, a)), (mod_((mul_(a, c)), m))));
	let temp_41_1 = (mul_((mod_((mul_(a, c)), m)), (mul_(d, a))));
	assert(eq_(temp_41_0, temp_41_1)) by {
		lemma_mul_comm(mul_(d, a), mod_(mul_(a, c), m));
	}
	let temp_42_0 = (mul_((mul_(b, a)), (mul_(c, b))));
	let temp_42_1 = (mul_((mul_((mul_(b, a)), c)), b));
	assert(eq_(temp_42_0, temp_42_1)) by {
		lemma_mul_assoc(mul_(b, a), c, b);
	}
	let temp_43_0 = (mul_((mul_(c, d)), (mul_(b, d))));
	let temp_43_1 = (mul_((mul_(d, c)), (mul_(b, d))));
	assert(eq_(temp_43_0, temp_43_1)) by {
		cong_mul_(mul_(c, d), mul_(b, d), mul_(d, c), mul_(b, d));
		lemma_mul_comm(c, d);
		lemma_eq_ref(mul_(b, d));
	}
	let temp_44_0 = (mul_((mul_(d, c)), (mul_(d, a))));
	let temp_44_1 = (mul_((mul_((mul_(d, c)), d)), a));
	assert(eq_(temp_44_0, temp_44_1)) by {
		lemma_mul_assoc(mul_(d, c), d, a);
	}
	let temp_45_0 = (add_((add_(a, (mod_(c, m)))), (mul_(d, c))));
	let temp_45_1 = (add_((add_(a, (mod_((add_(c, (mul_((mul_((mul_(b, d)), (mul_(d, d)))), m)))), m)))), (mul_(d, c))));
	assert(eq_(temp_45_0, temp_45_1)) by {
		lemma_mul_comm(c, d);
		lemma_mul_comm(d, c);
		lemma_mod_mul_vanish(c, mul_(mul_(b, d), mul_(d, d)), m);
		cong_add_(add_(a, mod_(c, m)), mul_(d, c), add_(a, mod_(add_(c, mul_(mul_(mul_(b, d), mul_(d, d)), m)), m)), mul_(d, c));
		lemma_eq_ref(a);
		lemma_eq_trans(mul_(d, c), mul_(c, d), mul_(d, c));
		cong_add_(a, mod_(c, m), a, mod_(add_(c, mul_(mul_(mul_(b, d), mul_(d, d)), m)), m));
	}
	let temp_46_0 = (mul_((mul_((mod_(b, m)), a)), (add_(b, (mod_(a, m))))));
	let temp_46_1 = (mul_((mul_((mod_(b, m)), a)), (add_(b, (mod_((sub_(a, (mul_((mul_((mul_(a, d)), (mul_(d, c)))), m)))), m))))));
	assert(eq_(temp_46_0, temp_46_1)) by {
		lemma_mod_mul_vanish(a, mul_(mul_(a, d), mul_(d, c)), m);
		cong_mul_(mul_(mod_(b, m), a), add_(b, mod_(a, m)), mul_(mod_(b, m), a), add_(b, mod_(sub_(a, mul_(mul_(mul_(a, d), mul_(d, c)), m)), m)));
		lemma_eq_ref(mul_(mod_(b, m), a));
		cong_add_(b, mod_(a, m), b, mod_(sub_(a, mul_(mul_(mul_(a, d), mul_(d, c)), m)), m));
		lemma_eq_ref(b);
	}
	let temp_47_0 = (mul_((mul_(c, d)), (mul_((mod_(c, m)), b))));
	let temp_47_1 = (mul_((mul_((mul_(c, d)), (mod_(c, m)))), b));
	assert(eq_(temp_47_0, temp_47_1)) by {
		lemma_mul_assoc(mul_(c, d), mod_(c, m), b);
	}
	let temp_48_0 = (mul_((mul_(d, c)), (sub_(as_elem(30), c))));
	let temp_48_1 = (mul_((mul_(c, d)), (sub_(as_elem(30), c))));
	assert(eq_(temp_48_0, temp_48_1)) by {
		cong_mul_(mul_(d, c), sub_(as_elem(30), c), mul_(c, d), sub_(as_elem(30), c));
		lemma_mul_comm(d, c);
		lemma_eq_ref(sub_(as_elem(30), c));
	}
	let temp_49_0 = (mul_((sub_(c, a)), (mul_(b, c))));
	let temp_49_1 = (mul_((sub_(c, a)), (mul_(c, b))));
	assert(eq_(temp_49_0, temp_49_1)) by {
		cong_mul_(sub_(c, a), mul_(b, c), sub_(c, a), mul_(c, b));
		lemma_mul_comm(b, c);
		lemma_eq_ref(sub_(c, a));
	}
	let temp_50_0 = (mul_((mul_(c, c)), (mul_((mod_(b, m)), c))));
	let temp_50_1 = (mul_(c, (mul_(c, (mul_((mod_(b, m)), c))))));
	assert(eq_(temp_50_0, temp_50_1)) by {
		lemma_eq_sym(temp_50_1, temp_50_0);
		lemma_mul_assoc(c, c, mul_(mod_(b, m), c));
	}
	let temp_51_0 = (mul_((add_(a, d)), (mul_(c, as_elem(60)))));
	let temp_51_1 = (mul_((mul_((add_(a, d)), c)), as_elem(60)));
	assert(eq_(temp_51_0, temp_51_1)) by {
		lemma_mul_assoc(add_(a, d), c, as_elem(60));
	}
	let temp_52_0 = (mul_((mul_(d, a)), (sub_(b, a))));
	let temp_52_1 = (mul_(d, (mul_(a, (sub_(b, a))))));
	assert(eq_(temp_52_0, temp_52_1)) by {
		lemma_eq_sym(temp_52_1, temp_52_0);
		lemma_mul_assoc(d, a, sub_(b, a));
	}
	let temp_53_0 = (mul_((mul_(a, b)), (mul_(b, d))));
	let temp_53_1 = (mul_(a, (mul_(b, (mul_(b, d))))));
	assert(eq_(temp_53_0, temp_53_1)) by {
		lemma_eq_sym(temp_53_1, temp_53_0);
		lemma_mul_assoc(a, b, mul_(b, d));
	}
	let temp_54_0 = (mul_((mul_(c, d)), (mul_((mod_(d, m)), a))));
	let temp_54_1 = (mul_((mul_(c, d)), (mul_((mod_((add_(d, (mul_((mul_((mul_(c, a)), (add_(d, b)))), m)))), m)), a))));
	assert(eq_(temp_54_0, temp_54_1)) by {
		lemma_mod_mul_vanish(d, mul_(mul_(c, a), add_(d, b)), m);
		cong_mul_(mul_(c, d), mul_(mod_(d, m), a), mul_(c, d), mul_(mod_(add_(d, mul_(mul_(mul_(c, a), add_(d, b)), m)), m), a));
		lemma_eq_ref(a);
		lemma_eq_ref(mul_(c, d));
		cong_mul_(mod_(d, m), a, mod_(add_(d, mul_(mul_(mul_(c, a), add_(d, b)), m)), m), a);
	}
	let temp_55_0 = (sub_((mod_((mul_(b, a)), m)), (mul_(c, (mod_(d, m))))));
	let temp_55_1 = (sub_((mod_((mul_(b, a)), m)), (mul_(c, (mod_((add_((mul_((mul_((sub_(a, a)), (mul_(b, b)))), m)), d)), m))))));
	assert(eq_(temp_55_0, temp_55_1)) by {
		lemma_mod_mul_vanish(d, mul_(sub_(a, a), mul_(b, b)), m);
		cong_sub_(mod_(mul_(b, a), m), mul_(c, mod_(d, m)), mod_(mul_(b, a), m), mul_(c, mod_(add_(mul_(mul_(sub_(a, a), mul_(b, b)), m), d), m)));
		cong_mul_(c, mod_(d, m), c, mod_(add_(mul_(mul_(sub_(a, a), mul_(b, b)), m), d), m));
		lemma_eq_ref(c);
		lemma_eq_ref(mod_(mul_(b, a), m));
	}
	let temp_56_0 = (mul_((add_(d, (mod_(c, m)))), (mul_(c, a))));
	let temp_56_1 = (mul_((mul_(c, a)), (add_(d, (mod_(c, m))))));
	assert(eq_(temp_56_0, temp_56_1)) by {
		lemma_mul_comm(add_(d, mod_(c, m)), mul_(c, a));
	}
	let temp_57_0 = (mul_((sub_(d, d)), (mul_(c, c))));
	let temp_57_1 = (mul_((mul_(c, c)), (sub_(d, d))));
	assert(eq_(temp_57_0, temp_57_1)) by {
		lemma_mul_comm(sub_(d, d), mul_(c, c));
	}
	let temp_58_0 = (mul_((mul_(d, b)), (mul_(d, a))));
	let temp_58_1 = (mul_((mul_(b, d)), (mul_(d, a))));
	assert(eq_(temp_58_0, temp_58_1)) by {
		cong_mul_(mul_(d, b), mul_(d, a), mul_(b, d), mul_(d, a));
		lemma_mul_comm(d, b);
		lemma_eq_ref(mul_(d, a));
	}
	let temp_59_0 = (mul_((mul_(c, d)), (mul_(b, d))));
	let temp_59_1 = (mul_((mul_(b, d)), (mul_(c, d))));
	assert(eq_(temp_59_0, temp_59_1)) by {
		lemma_mul_comm(mul_(c, d), mul_(b, d));
	}
	let temp_60_0 = (sub_((mul_(a, (mod_(a, m)))), (mul_(b, d))));
	let temp_60_1 = (sub_((mul_(a, (mod_((add_((mul_((mod_((mul_((mul_(a, d)), (add_(c, b)))), m)), m)), a)), m)))), (mul_(b, d))));
	assert(eq_(temp_60_0, temp_60_1)) by {
		lemma_mod_mul_vanish(a, mod_(mul_(mul_(a, d), add_(c, b)), m), m);
		cong_sub_(mul_(a, mod_(a, m)), mul_(b, d), mul_(a, mod_(add_(mul_(mod_(mul_(mul_(a, d), add_(c, b)), m), m), a), m)), mul_(b, d));
		cong_mul_(a, mod_(a, m), a, mod_(add_(mul_(mod_(mul_(mul_(a, d), add_(c, b)), m), m), a), m));
		lemma_eq_ref(mul_(b, d));
		lemma_eq_ref(a);
	}
	let temp_61_0 = (mod_((sub_((mul_(d, (mod_(c, m)))), (mul_(c, (mod_(c, m)))))), m));
	let temp_61_1 = (mod_((sub_((mul_(d, (mod_(c, m)))), (mod_((mul_(c, (mod_(c, m)))), m)))), m));
	assert(eq_(temp_61_0, temp_61_1)) by {
		lemma_mod_sub_noop(mul_(d, mod_(c, m)), mul_(c, mod_(c, m)), m);
	}
	let temp_62_0 = (mul_((mul_(c, c)), (mod_((mul_(c, d)), m))));
	let temp_62_1 = (mul_((mul_(c, c)), (mod_((sub_((mul_(c, d)), (mul_((mul_((mul_(c, c)), (mul_(b, b)))), m)))), m))));
	assert(eq_(temp_62_0, temp_62_1)) by {
		lemma_mul_comm(c, c);
		cong_mul_(mul_(c, c), mod_(mul_(c, d), m), mul_(c, c), mod_(sub_(mul_(c, d), mul_(mul_(mul_(c, c), mul_(b, b)), m)), m));
		lemma_mod_mul_vanish(mul_(c, d), mul_(mul_(c, c), mul_(b, b)), m);
	}
	let temp_63_0 = (mul_((mul_(a, d)), (mod_((mul_(a, d)), m))));
	let temp_63_1 = (mul_(a, (mul_(d, (mod_((mul_(a, d)), m))))));
	assert(eq_(temp_63_0, temp_63_1)) by {
		lemma_eq_sym(temp_63_1, temp_63_0);
		lemma_mul_assoc(a, d, mod_(mul_(a, d), m));
	}
	let temp_64_0 = (add_((mul_(d, (mod_(b, m)))), (mod_((mul_(d, b)), m))));
	let temp_64_1 = (add_((mul_(d, (mod_((sub_(b, (mul_((mul_((mul_(c, (mod_(d, m)))), (mul_(a, d)))), m)))), m)))), (mod_((mul_(d, b)), m))));
	assert(eq_(temp_64_0, temp_64_1)) by {
		cong_add_(mul_(d, mod_(b, m)), mod_(mul_(d, b), m), mul_(d, mod_(sub_(b, mul_(mul_(mul_(c, mod_(d, m)), mul_(a, d)), m)), m)), mod_(mul_(d, b), m));
		lemma_mod_mul_vanish(b, mul_(mul_(c, mod_(d, m)), mul_(a, d)), m);
		lemma_eq_ref(d);
		cong_mul_(d, mod_(b, m), d, mod_(sub_(b, mul_(mul_(mul_(c, mod_(d, m)), mul_(a, d)), m)), m));
		lemma_eq_ref(mod_(mul_(d, b), m));
	}
	let temp_65_0 = (add_((mod_((sub_(d, a)), m)), (mul_(d, d))));
	let temp_65_1 = (add_((mul_(d, d)), (mod_((sub_(d, a)), m))));
	assert(eq_(temp_65_0, temp_65_1)) by {
		lemma_add_comm(mod_(sub_(d, a), m), mul_(d, d));
	}
	let temp_66_0 = (mul_((mul_(c, (mod_(b, m)))), (mul_(b, d))));
	let temp_66_1 = (mul_((mul_((mod_(b, m)), c)), (mul_(b, d))));
	assert(eq_(temp_66_0, temp_66_1)) by {
		lemma_mul_comm(c, mod_(b, m));
		cong_mul_(mul_(c, mod_(b, m)), mul_(b, d), mul_(mod_(b, m), c), mul_(b, d));
		lemma_eq_ref(mul_(b, d));
	}
	let temp_67_0 = (mul_((mul_(c, a)), (mod_((sub_(d, c)), m))));
	let temp_67_1 = (mul_((mul_(c, a)), (mod_((add_((sub_(d, c)), (mul_((sub_((mul_(a, b)), (mul_(b, c)))), m)))), m))));
	assert(eq_(temp_67_0, temp_67_1)) by {
		lemma_mod_mul_vanish(sub_(d, c), sub_(mul_(a, b), mul_(b, c)), m);
		cong_mul_(mul_(c, a), mod_(sub_(d, c), m), mul_(c, a), mod_(add_(sub_(d, c), mul_(sub_(mul_(a, b), mul_(b, c)), m)), m));
		lemma_eq_ref(mul_(c, a));
	}
	let temp_68_0 = (mul_((mul_(b, (mod_(c, m)))), (mod_((mul_(a, c)), m))));
	let temp_68_1 = (mul_(b, (mul_((mod_(c, m)), (mod_((mul_(a, c)), m))))));
	assert(eq_(temp_68_0, temp_68_1)) by {
		lemma_mul_assoc(b, mod_(c, m), mod_(mul_(a, c), m));
		lemma_eq_sym(temp_68_1, temp_68_0);
	}
	let temp_69_0 = (add_((mul_(b, a)), (mul_(b, b))));
	let temp_69_1 = (mul_(b, (add_(a, b))));
	assert(eq_(temp_69_0, temp_69_1)) by {
		lemma_eq_sym(temp_69_1, temp_69_0);
		lemma_mul_dist(b, a, b);
	}
	let temp_70_0 = (mod_((mul_((sub_(as_elem(93), b)), (mul_(b, c)))), m));
	let temp_70_1 = (mod_((mul_((mul_(b, c)), (sub_(as_elem(93), b)))), m));
	assert(eq_(temp_70_0, temp_70_1)) by {
		lemma_mul_comm(sub_(as_elem(93), b), mul_(b, c));
		cong_mod_(mul_(sub_(as_elem(93), b), mul_(b, c)), m, mul_(mul_(b, c), sub_(as_elem(93), b)), m);
		lemma_eq_ref(m);
	}
	let temp_71_0 = (mul_((mul_((mod_(a, m)), c)), (mul_(d, c))));
	let temp_71_1 = (mul_((mul_((mod_((sub_(a, (mul_((mul_((add_(a, as_elem(84))), (sub_(a, (mod_(as_elem(80), m)))))), m)))), m)), c)), (mul_(d, c))));
	assert(eq_(temp_71_0, temp_71_1)) by {
		cong_mul_(mul_(mod_(a, m), c), mul_(d, c), mul_(mod_(sub_(a, mul_(mul_(add_(a, as_elem(84)), sub_(a, mod_(as_elem(80), m))), m)), m), c), mul_(d, c));
		lemma_mod_mul_vanish(a, mul_(add_(a, as_elem(84)), sub_(a, mod_(as_elem(80), m))), m);
		cong_mul_(mod_(a, m), c, mod_(sub_(a, mul_(mul_(add_(a, as_elem(84)), sub_(a, mod_(as_elem(80), m))), m)), m), c);
		lemma_eq_ref(mul_(d, c));
		lemma_eq_ref(c);
	}
	let temp_72_0 = (add_((mul_((mod_(a, m)), d)), (mul_((mod_(d, m)), b))));
	let temp_72_1 = (add_((mul_((mod_((add_((mul_((mod_((mul_((add_(a, a)), d)), m)), m)), a)), m)), d)), (mul_((mod_(d, m)), b))));
	assert(eq_(temp_72_0, temp_72_1)) by {
		lemma_mod_mul_vanish(a, mod_(mul_(add_(a, a), d), m), m);
		cong_add_(mul_(mod_(a, m), d), mul_(mod_(d, m), b), mul_(mod_(add_(mul_(mod_(mul_(add_(a, a), d), m), m), a), m), d), mul_(mod_(d, m), b));
		lemma_eq_ref(d);
		cong_mul_(mod_(a, m), d, mod_(add_(mul_(mod_(mul_(add_(a, a), d), m), m), a), m), d);
		lemma_eq_ref(mul_(mod_(d, m), b));
	}
	let temp_73_0 = (sub_((mul_(d, b)), (mul_(b, b))));
	let temp_73_1 = (sub_((mul_(b, d)), (mul_(b, b))));
	assert(eq_(temp_73_0, temp_73_1)) by {
		cong_sub_(mul_(d, b), mul_(b, b), mul_(b, d), mul_(b, b));
		lemma_mul_comm(d, b);
		lemma_mul_comm(b, b);
	}
	let temp_74_0 = (mul_(b, (mul_((mod_(d, m)), c))));
	let temp_74_1 = (mul_(b, (mul_(c, (mod_(d, m))))));
	assert(eq_(temp_74_0, temp_74_1)) by {
		cong_mul_(b, mul_(mod_(d, m), c), b, mul_(c, mod_(d, m)));
		lemma_mul_comm(mod_(d, m), c);
		lemma_eq_ref(b);
	}
	let temp_75_0 = (mul_((mul_(d, a)), (mul_(b, (mod_(d, m))))));
	let temp_75_1 = (mul_((mul_(d, a)), (mul_(b, (mod_((sub_(d, (mul_((mul_((mul_(b, d)), (mod_((mul_((mod_(a, m)), c)), m)))), m)))), m))))));
	assert(eq_(temp_75_0, temp_75_1)) by {
		lemma_eq_ref(mul_(d, a));
		cong_mul_(mul_(d, a), mul_(b, mod_(d, m)), mul_(d, a), mul_(b, mod_(sub_(d, mul_(mul_(mul_(b, d), mod_(mul_(mod_(a, m), c), m)), m)), m)));
		lemma_mod_mul_vanish(d, mul_(mul_(b, d), mod_(mul_(mod_(a, m), c), m)), m);
		lemma_eq_ref(b);
		cong_mul_(b, mod_(d, m), b, mod_(sub_(d, mul_(mul_(mul_(b, d), mod_(mul_(mod_(a, m), c), m)), m)), m));
	}
	let temp_76_0 = (mod_((add_((mul_(d, d)), (mul_((mod_(d, m)), b)))), m));
	let temp_76_1 = (mod_((add_((mul_((mod_(d, m)), b)), (mul_(d, d)))), m));
	assert(eq_(temp_76_0, temp_76_1)) by {
		lemma_add_comm(mul_(d, d), mul_(mod_(d, m), b));
		cong_mod_(add_(mul_(d, d), mul_(mod_(d, m), b)), m, add_(mul_(mod_(d, m), b), mul_(d, d)), m);
		lemma_eq_ref(m);
	}
	let temp_77_0 = (mul_((mul_(b, c)), (mul_(as_elem(5), a))));
	let temp_77_1 = (mul_((mul_(as_elem(5), a)), (mul_(b, c))));
	assert(eq_(temp_77_0, temp_77_1)) by {
		lemma_mul_comm(mul_(b, c), mul_(as_elem(5), a));
	}
	let temp_78_0 = (mul_((mod_((mul_(b, c)), m)), (mul_(c, a))));
	let temp_78_1 = (mul_((mul_(c, a)), (mod_((mul_(b, c)), m))));
	assert(eq_(temp_78_0, temp_78_1)) by {
		lemma_mul_comm(mod_(mul_(b, c), m), mul_(c, a));
	}
	let temp_79_0 = (add_((mul_((mod_(d, m)), d)), (mul_((mod_(a, m)), b))));
	let temp_79_1 = (add_((mul_((mod_(a, m)), b)), (mul_((mod_(d, m)), d))));
	assert(eq_(temp_79_0, temp_79_1)) by {
		lemma_add_comm(mul_(mod_(d, m), d), mul_(mod_(a, m), b));
	}
	let temp_80_0 = (mod_((mul_((sub_(b, a)), (mul_(d, c)))), m));
	let temp_80_1 = (mod_((mul_((mul_((sub_(b, a)), d)), c)), m));
	assert(eq_(temp_80_0, temp_80_1)) by {
		lemma_mul_assoc(sub_(b, a), d, c);
		cong_mod_(mul_(sub_(b, a), mul_(d, c)), m, mul_(mul_(sub_(b, a), d), c), m);
		lemma_eq_ref(m);
	}
	let temp_81_0 = (mod_((mul_((mul_(b, a)), (mul_(c, a)))), m));
	let temp_81_1 = (mod_((add_((mul_((mul_((mul_(a, d)), (mul_(c, b)))), m)), (mul_((mul_(b, a)), (mul_(c, a)))))), m));
	assert(eq_(temp_81_0, temp_81_1)) by {
		lemma_mod_mul_vanish(mul_(mul_(b, a), mul_(c, a)), mul_(mul_(a, d), mul_(c, b)), m);
	}
	let temp_82_0 = (mul_((mul_(d, c)), (mul_(as_elem(99), d))));
	let temp_82_1 = (mul_((mul_((mul_(d, c)), as_elem(99))), d));
	assert(eq_(temp_82_0, temp_82_1)) by {
		lemma_mul_assoc(mul_(d, c), as_elem(99), d);
	}
	let temp_83_0 = (mul_((mul_(c, c)), (mul_(b, c))));
	let temp_83_1 = (mul_((mul_(c, c)), (mul_(c, b))));
	assert(eq_(temp_83_0, temp_83_1)) by {
		cong_mul_(mul_(c, c), mul_(b, c), mul_(c, c), mul_(c, b));
		lemma_mul_comm(c, c);
		lemma_mul_comm(b, c);
	}
	let temp_84_0 = (mul_((mul_(d, b)), (mul_(a, a))));
	let temp_84_1 = (mul_((mul_((mul_(d, b)), a)), a));
	assert(eq_(temp_84_0, temp_84_1)) by {
		lemma_mul_assoc(mul_(d, b), a, a);
	}
	let temp_85_0 = (mul_((mul_(d, a)), (mul_(as_elem(97), c))));
	let temp_85_1 = (mul_((mul_(a, d)), (mul_(as_elem(97), c))));
	assert(eq_(temp_85_0, temp_85_1)) by {
		lemma_mul_comm(d, a);
		cong_mul_(mul_(d, a), mul_(as_elem(97), c), mul_(a, d), mul_(as_elem(97), c));
		lemma_eq_ref(mul_(as_elem(97), c));
	}
	let temp_86_0 = (mul_((sub_(d, b)), (mul_((mod_(as_elem(98), m)), a))));
	let temp_86_1 = (mul_((sub_(d, b)), (mul_((mod_((sub_(as_elem(98), (mul_((mul_((add_(b, c)), (mul_((mod_(b, m)), (mod_(c, m)))))), m)))), m)), a))));
	assert(eq_(temp_86_0, temp_86_1)) by {
		cong_mul_(sub_(d, b), mul_(mod_(as_elem(98), m), a), sub_(d, b), mul_(mod_(sub_(as_elem(98), mul_(mul_(add_(b, c), mul_(mod_(b, m), mod_(c, m))), m)), m), a));
		lemma_mod_mul_vanish(as_elem(98), mul_(add_(b, c), mul_(mod_(b, m), mod_(c, m))), m);
		lemma_eq_ref(sub_(d, b));
		cong_mul_(mod_(as_elem(98), m), a, mod_(sub_(as_elem(98), mul_(mul_(add_(b, c), mul_(mod_(b, m), mod_(c, m))), m)), m), a);
		lemma_eq_ref(a);
	}
	let temp_87_0 = (mul_((sub_(d, as_elem(98))), (mul_(a, c))));
	let temp_87_1 = (sub_((mul_(d, (mul_(a, c)))), (mul_(as_elem(98), (mul_(a, c))))));
	assert(eq_(temp_87_0, temp_87_1)) by {
		lemma_mul_dist(mul_(a, c), d, as_elem(98));
	}
	let temp_88_0 = (mod_((add_((mul_(b, a)), (add_(a, a)))), m));
	let temp_88_1 = (mod_((add_((mul_(a, b)), (add_(a, a)))), m));
	assert(eq_(temp_88_0, temp_88_1)) by {
		lemma_mul_comm(b, a);
		cong_mod_(add_(mul_(b, a), add_(a, a)), m, add_(mul_(a, b), add_(a, a)), m);
		lemma_eq_ref(add_(a, a));
		cong_add_(mul_(b, a), add_(a, a), mul_(a, b), add_(a, a));
		lemma_eq_ref(m);
	}
	let temp_89_0 = (mul_((mul_(a, c)), (mul_(c, as_elem(76)))));
	let temp_89_1 = (mul_((mul_(c, as_elem(76))), (mul_(a, c))));
	assert(eq_(temp_89_0, temp_89_1)) by {
		lemma_mul_comm(mul_(a, c), mul_(c, as_elem(76)));
	}
	let temp_90_0 = (mul_((mul_(c, a)), (mul_((mod_(d, m)), a))));
	let temp_90_1 = (mul_((mul_(c, a)), (mul_((mod_((sub_(d, (mul_((mul_((mul_(a, c)), (add_(c, (mod_(c, m)))))), m)))), m)), a))));
	assert(eq_(temp_90_0, temp_90_1)) by {
		lemma_mod_mul_vanish(d, mul_(mul_(a, c), add_(c, mod_(c, m))), m);
		cong_mul_(mul_(c, a), mul_(mod_(d, m), a), mul_(c, a), mul_(mod_(sub_(d, mul_(mul_(mul_(a, c), add_(c, mod_(c, m))), m)), m), a));
		lemma_eq_ref(a);
		lemma_eq_ref(mul_(c, a));
		cong_mul_(mod_(d, m), a, mod_(sub_(d, mul_(mul_(mul_(a, c), add_(c, mod_(c, m))), m)), m), a);
	}
	let temp_91_0 = (mul_((sub_(b, a)), (mod_((mul_(b, as_elem(26))), m))));
	let temp_91_1 = (sub_((mul_(b, (mod_((mul_(b, as_elem(26))), m)))), (mul_(a, (mod_((mul_(b, as_elem(26))), m))))));
	assert(eq_(temp_91_0, temp_91_1)) by {
		lemma_mul_dist(mod_(mul_(b, as_elem(26)), m), b, a);
	}
	let temp_92_0 = (mul_((mul_(c, (mod_(d, m)))), (mul_(c, a))));
	let temp_92_1 = (mul_((mul_(c, a)), (mul_(c, (mod_(d, m))))));
	assert(eq_(temp_92_0, temp_92_1)) by {
		lemma_mul_comm(mul_(c, mod_(d, m)), mul_(c, a));
	}
	let temp_93_0 = (mul_((mul_(a, c)), (mod_((mul_(b, d)), m))));
	let temp_93_1 = (mul_((mul_(a, c)), (mod_((add_((mul_(b, d)), (mul_((mul_((mul_(d, a)), (mul_(a, (mod_(c, m)))))), m)))), m))));
	assert(eq_(temp_93_0, temp_93_1)) by {
		lemma_mod_mul_vanish(mul_(b, d), mul_(mul_(d, a), mul_(a, mod_(c, m))), m);
		cong_mul_(mul_(a, c), mod_(mul_(b, d), m), mul_(a, c), mod_(add_(mul_(b, d), mul_(mul_(mul_(d, a), mul_(a, mod_(c, m))), m)), m));
		lemma_eq_ref(mul_(a, c));
	}
	let temp_94_0 = (mul_((mul_(d, a)), (mul_(c, c))));
	let temp_94_1 = (mul_(d, (mul_(a, (mul_(c, c))))));
	assert(eq_(temp_94_0, temp_94_1)) by {
		lemma_eq_sym(temp_94_1, temp_94_0);
		lemma_mul_assoc(d, a, mul_(c, c));
	}
	let temp_95_0 = (sub_((add_(d, c)), (mul_(c, as_elem(11)))));
	let temp_95_1 = (sub_((add_(c, d)), (mul_(c, as_elem(11)))));
	assert(eq_(temp_95_0, temp_95_1)) by {
		lemma_add_comm(d, c);
		cong_sub_(add_(d, c), mul_(c, as_elem(11)), add_(c, d), mul_(c, as_elem(11)));
		lemma_eq_ref(mul_(c, as_elem(11)));
	}
	let temp_96_0 = (mul_((mul_(a, d)), (mul_(b, b))));
	let temp_96_1 = (mul_((mul_((mul_(a, d)), b)), b));
	assert(eq_(temp_96_0, temp_96_1)) by {
		lemma_mul_assoc(mul_(a, d), b, b);
	}
	let temp_97_0 = (mul_((mul_(b, d)), (add_(b, d))));
	let temp_97_1 = (add_((mul_((mul_(b, d)), b)), (mul_((mul_(b, d)), d))));
	assert(eq_(temp_97_0, temp_97_1)) by {
		lemma_mul_dist(mul_(b, d), b, d);
	}
	let temp_98_0 = (mul_((mul_(c, d)), (mul_(d, (mod_(d, m))))));
	let temp_98_1 = (mul_((mul_((mul_(c, d)), d)), (mod_(d, m))));
	assert(eq_(temp_98_0, temp_98_1)) by {
		lemma_mul_assoc(mul_(c, d), d, mod_(d, m));
	}
	let temp_99_0 = (mul_((mul_(c, b)), (mul_(a, c))));
	let temp_99_1 = (mul_(c, (mul_(b, (mul_(a, c))))));
	assert(eq_(temp_99_0, temp_99_1)) by {
		lemma_eq_sym(temp_99_1, temp_99_0);
		lemma_mul_assoc(c, b, mul_(a, c));
	}
	let temp_100_0 = (sub_((mul_(c, d)), (mul_(d, d))));
	let temp_100_1 = (mul_((sub_(c, d)), d));
	assert(eq_(temp_100_0, temp_100_1)) by {
		lemma_eq_sym(temp_100_1, temp_100_0);
		lemma_mul_dist(d, c, d);
	}
	let temp_101_0 = (mul_((mul_(d, a)), (mod_((mul_(c, a)), m))));
	let temp_101_1 = (mul_((mul_(d, a)), (mod_((add_((mul_((mul_((mul_(c, c)), (mul_(b, c)))), m)), (mul_(c, a)))), m))));
	assert(eq_(temp_101_0, temp_101_1)) by {
		lemma_mod_mul_vanish(mul_(c, a), mul_(mul_(c, c), mul_(b, c)), m);
		cong_mul_(mul_(d, a), mod_(mul_(c, a), m), mul_(d, a), mod_(add_(mul_(mul_(mul_(c, c), mul_(b, c)), m), mul_(c, a)), m));
		lemma_eq_ref(mul_(d, a));
	}
	let temp_102_0 = (mul_((mul_(b, (mod_(a, m)))), (mul_(a, as_elem(25)))));
	let temp_102_1 = (mul_((mul_(b, (mod_((sub_(a, (mul_((mod_((mul_((mul_(a, b)), (mul_((mod_(d, m)), (mod_(d, m)))))), m)), m)))), m)))), (mul_(a, as_elem(25)))));
	assert(eq_(temp_102_0, temp_102_1)) by {
		lemma_mod_mul_vanish(a, mod_(mul_(mul_(a, b), mul_(mod_(d, m), mod_(d, m))), m), m);
		cong_mul_(mul_(b, mod_(a, m)), mul_(a, as_elem(25)), mul_(b, mod_(sub_(a, mul_(mod_(mul_(mul_(a, b), mul_(mod_(d, m), mod_(d, m))), m), m)), m)), mul_(a, as_elem(25)));
		lemma_eq_ref(b);
		cong_mul_(b, mod_(a, m), b, mod_(sub_(a, mul_(mod_(mul_(mul_(a, b), mul_(mod_(d, m), mod_(d, m))), m), m)), m));
		lemma_eq_ref(mul_(a, as_elem(25)));
	}
	let temp_103_0 = (mul_((mul_(c, d)), (mul_(d, d))));
	let temp_103_1 = (mul_((mul_((mul_(c, d)), d)), d));
	assert(eq_(temp_103_0, temp_103_1)) by {
		lemma_mul_assoc(mul_(c, d), d, d);
	}
	let temp_104_0 = (mul_((mul_(c, a)), (add_(d, b))));
	let temp_104_1 = (mul_(c, (mul_(a, (add_(d, b))))));
	assert(eq_(temp_104_0, temp_104_1)) by {
		lemma_eq_sym(temp_104_1, temp_104_0);
		lemma_mul_assoc(c, a, add_(d, b));
	}
	let temp_105_0 = (sub_((mul_(a, b)), (add_(c, b))));
	let temp_105_1 = (sub_((mul_(b, a)), (add_(c, b))));
	assert(eq_(temp_105_0, temp_105_1)) by {
		cong_sub_(mul_(a, b), add_(c, b), mul_(b, a), add_(c, b));
		lemma_mul_comm(a, b);
		lemma_eq_ref(add_(c, b));
	}
	let temp_106_0 = (mul_((add_(c, b)), (mul_(d, c))));
	let temp_106_1 = (mul_((add_(c, b)), (mul_(c, d))));
	assert(eq_(temp_106_0, temp_106_1)) by {
		cong_mul_(add_(c, b), mul_(d, c), add_(c, b), mul_(c, d));
		lemma_mul_comm(d, c);
		lemma_eq_ref(add_(c, b));
	}
	let temp_107_0 = (mul_((add_(d, a)), (mod_((mul_(a, a)), m))));
	let temp_107_1 = (add_((mul_(d, (mod_((mul_(a, a)), m)))), (mul_(a, (mod_((mul_(a, a)), m))))));
	assert(eq_(temp_107_0, temp_107_1)) by {
		lemma_mul_dist(d, a, mod_(mul_(a, a), m));
	}
	let temp_108_0 = (mul_((mul_(d, b)), (mul_(d, b))));
	let temp_108_1 = (mul_((mul_(d, b)), (mul_(d, b))));
	assert(eq_(temp_108_0, temp_108_1)) by {
		lemma_eq_ref(temp_108_0);
	}
	let temp_109_0 = (add_((mul_(d, a)), (mul_(d, d))));
	let temp_109_1 = (add_((mul_(a, d)), (mul_(d, d))));
	assert(eq_(temp_109_0, temp_109_1)) by {
		cong_add_(mul_(d, a), mul_(d, d), mul_(a, d), mul_(d, d));
		lemma_mul_comm(d, a);
		lemma_eq_ref(mul_(d, d));
	}
	let temp_110_0 = (mul_((mul_((mod_(c, m)), b)), (mul_(a, d))));
	let temp_110_1 = (mul_((mul_((mul_((mod_(c, m)), b)), a)), d));
	assert(eq_(temp_110_0, temp_110_1)) by {
		lemma_mul_assoc(mul_(mod_(c, m), b), a, d);
	}
	let temp_111_0 = (add_((add_(b, d)), (mul_(d, b))));
	let temp_111_1 = (add_((add_(b, d)), (mul_(b, d))));
	assert(eq_(temp_111_0, temp_111_1)) by {
		cong_add_(add_(b, d), mul_(d, b), add_(b, d), mul_(b, d));
		lemma_mul_comm(d, b);
		lemma_eq_ref(add_(b, d));
	}
	let temp_112_0 = (sub_((mul_(b, c)), (mul_(d, a))));
	let temp_112_1 = (sub_((mul_(c, b)), (mul_(d, a))));
	assert(eq_(temp_112_0, temp_112_1)) by {
		cong_sub_(mul_(b, c), mul_(d, a), mul_(c, b), mul_(d, a));
		lemma_mul_comm(b, c);
		lemma_eq_ref(mul_(d, a));
	}
	let temp_113_0 = (mod_((sub_((mul_(c, a)), (mul_(c, b)))), m));
	let temp_113_1 = (mod_((add_((mul_((mul_((mul_(as_elem(61), c)), (mul_(c, b)))), m)), (sub_((mul_(c, a)), (mul_(c, b)))))), m));
	assert(eq_(temp_113_0, temp_113_1)) by {
		lemma_mod_mul_vanish(sub_(mul_(c, a), mul_(c, b)), mul_(mul_(as_elem(61), c), mul_(c, b)), m);
	}
	let temp_114_0 = (mul_((mul_(d, d)), (mod_((add_(a, b)), m))));
	let temp_114_1 = (mul_((mul_(d, d)), (mod_((add_((mul_((mul_((mul_(a, (mod_(b, m)))), (sub_(d, c)))), m)), (add_(a, b)))), m))));
	assert(eq_(temp_114_0, temp_114_1)) by {
		lemma_mul_comm(d, d);
		lemma_mod_mul_vanish(add_(a, b), mul_(mul_(a, mod_(b, m)), sub_(d, c)), m);
		cong_mul_(mul_(d, d), mod_(add_(a, b), m), mul_(d, d), mod_(add_(mul_(mul_(mul_(a, mod_(b, m)), sub_(d, c)), m), add_(a, b)), m));
	}
	let temp_115_0 = (mul_((mul_(d, b)), (mul_(b, (mod_(c, m))))));
	let temp_115_1 = (mul_((mul_(d, b)), (mul_(b, (mod_((sub_(c, (mul_((mul_((mul_(a, c)), (sub_(a, a)))), m)))), m))))));
	assert(eq_(temp_115_0, temp_115_1)) by {
		lemma_mod_mul_vanish(c, mul_(mul_(a, c), sub_(a, a)), m);
		cong_mul_(mul_(d, b), mul_(b, mod_(c, m)), mul_(d, b), mul_(b, mod_(sub_(c, mul_(mul_(mul_(a, c), sub_(a, a)), m)), m)));
		lemma_eq_ref(b);
		lemma_eq_ref(mul_(d, b));
		cong_mul_(b, mod_(c, m), b, mod_(sub_(c, mul_(mul_(mul_(a, c), sub_(a, a)), m)), m));
	}
	let temp_116_0 = (mul_((mul_(b, c)), (sub_(d, d))));
	let temp_116_1 = (mul_((mul_(c, b)), (sub_(d, d))));
	assert(eq_(temp_116_0, temp_116_1)) by {
		cong_mul_(mul_(b, c), sub_(d, d), mul_(c, b), sub_(d, d));
		lemma_mul_comm(b, c);
		lemma_eq_ref(sub_(d, d));
	}
	let temp_117_0 = (mod_((mul_((mul_(c, d)), (mul_(d, c)))), m));
	let temp_117_1 = (mod_((add_((mul_((add_((mul_(c, c)), (mul_((mod_(a, m)), b)))), m)), (mul_((mul_(c, d)), (mul_(d, c)))))), m));
	assert(eq_(temp_117_0, temp_117_1)) by {
		lemma_mod_mul_vanish(mul_(mul_(c, d), mul_(d, c)), add_(mul_(c, c), mul_(mod_(a, m), b)), m);
	}
	let temp_118_0 = (mul_((mod_((mul_(c, a)), m)), (mul_(a, c))));
	let temp_118_1 = (mul_((mul_((mod_((mul_(c, a)), m)), a)), c));
	assert(eq_(temp_118_0, temp_118_1)) by {
		lemma_mul_assoc(mod_(mul_(c, a), m), a, c);
	}
	let temp_119_0 = (mul_((mul_(a, c)), (mul_(d, d))));
	let temp_119_1 = (mul_((mul_(d, d)), (mul_(a, c))));
	assert(eq_(temp_119_0, temp_119_1)) by {
		lemma_mul_comm(mul_(a, c), mul_(d, d));
	}
	let temp_120_0 = (mul_((mod_((mul_(c, d)), m)), (mul_(b, d))));
	let temp_120_1 = (mul_((mod_((add_((mul_((mul_((mod_((mul_(c, d)), m)), (mul_((mod_(c, m)), b)))), m)), (mul_(c, d)))), m)), (mul_(b, d))));
	assert(eq_(temp_120_0, temp_120_1)) by {
		lemma_mod_mul_vanish(mul_(c, d), mul_(mod_(mul_(c, d), m), mul_(mod_(c, m), b)), m);
		cong_mul_(mod_(mul_(c, d), m), mul_(b, d), mod_(add_(mul_(mul_(mod_(mul_(c, d), m), mul_(mod_(c, m), b)), m), mul_(c, d)), m), mul_(b, d));
		lemma_eq_ref(mul_(b, d));
	}
	let temp_121_0 = (mul_((sub_(b, a)), (mul_(a, c))));
	let temp_121_1 = (mul_((mul_((sub_(b, a)), a)), c));
	assert(eq_(temp_121_0, temp_121_1)) by {
		lemma_mul_assoc(sub_(b, a), a, c);
	}
	let temp_122_0 = (sub_((mul_(a, (mod_(c, m)))), (mul_(a, (mod_(d, m))))));
	let temp_122_1 = (sub_((mul_(a, (mod_((add_(c, (mul_((mod_((mul_((mul_(c, a)), (mul_(a, d)))), m)), m)))), m)))), (mul_(a, (mod_(d, m))))));
	assert(eq_(temp_122_0, temp_122_1)) by {
		lemma_mod_mul_vanish(c, mod_(mul_(mul_(c, a), mul_(a, d)), m), m);
		cong_sub_(mul_(a, mod_(c, m)), mul_(a, mod_(d, m)), mul_(a, mod_(add_(c, mul_(mod_(mul_(mul_(c, a), mul_(a, d)), m), m)), m)), mul_(a, mod_(d, m)));
		lemma_eq_ref(a);
		cong_mul_(a, mod_(c, m), a, mod_(add_(c, mul_(mod_(mul_(mul_(c, a), mul_(a, d)), m), m)), m));
		lemma_eq_ref(mul_(a, mod_(d, m)));
	}
	let temp_123_0 = (mod_((mul_((mod_((mul_(d, a)), m)), (mul_(c, (mod_(c, m)))))), m));
	let temp_123_1 = (mod_((mul_((mul_(c, (mod_(c, m)))), (mod_((mul_(d, a)), m)))), m));
	assert(eq_(temp_123_0, temp_123_1)) by {
		lemma_mul_comm(mod_(mul_(d, a), m), mul_(c, mod_(c, m)));
		cong_mod_(mul_(mod_(mul_(d, a), m), mul_(c, mod_(c, m))), m, mul_(mul_(c, mod_(c, m)), mod_(mul_(d, a), m)), m);
		lemma_eq_ref(m);
	}
	let temp_124_0 = (mul_((mul_((mod_(b, m)), c)), c));
	let temp_124_1 = (mul_((mul_(c, (mod_(b, m)))), c));
	assert(eq_(temp_124_0, temp_124_1)) by {
		cong_mul_(mul_(mod_(b, m), c), c, mul_(c, mod_(b, m)), c);
		lemma_mul_comm(mod_(b, m), c);
		lemma_eq_ref(c);
	}
	let temp_125_0 = (add_((mod_((sub_((mod_(a, m)), b)), m)), (mul_(c, (mod_(a, m))))));
	let temp_125_1 = (add_((mod_((sub_((mod_(a, m)), b)), m)), (mul_((mod_(a, m)), c))));
	assert(eq_(temp_125_0, temp_125_1)) by {
		lemma_mul_comm(c, mod_(a, m));
		cong_add_(mod_(sub_(mod_(a, m), b), m), mul_(c, mod_(a, m)), mod_(sub_(mod_(a, m), b), m), mul_(mod_(a, m), c));
		lemma_eq_ref(mod_(sub_(mod_(a, m), b), m));
	}
	let temp_126_0 = (mul_(d, (mul_(b, c))));
	let temp_126_1 = (mul_((mul_(d, b)), c));
	assert(eq_(temp_126_0, temp_126_1)) by {
		lemma_mul_assoc(d, b, c);
	}
	let temp_127_0 = (sub_((mul_(a, a)), a));
	let temp_127_1 = (sub_((mul_(a, a)), a));
	assert(eq_(temp_127_0, temp_127_1)) by {
		lemma_eq_ref(temp_127_0);
	}
	let temp_128_0 = (mul_((mul_(b, a)), (mul_(as_elem(25), c))));
	let temp_128_1 = (mul_((mul_((mul_(b, a)), as_elem(25))), c));
	assert(eq_(temp_128_0, temp_128_1)) by {
		lemma_mul_assoc(mul_(b, a), as_elem(25), c);
	}
	let temp_129_0 = (mul_((mul_(b, d)), (mul_(c, a))));
	let temp_129_1 = (mul_((mul_(b, d)), (mul_(a, c))));
	assert(eq_(temp_129_0, temp_129_1)) by {
		cong_mul_(mul_(b, d), mul_(c, a), mul_(b, d), mul_(a, c));
		lemma_mul_comm(c, a);
		lemma_eq_ref(mul_(b, d));
	}
	let temp_130_0 = (mod_((mul_((mul_(d, d)), (mul_(d, b)))), m));
	let temp_130_1 = (mod_((mul_((mul_(d, d)), (mul_(d, b)))), m));
	assert(eq_(temp_130_0, temp_130_1)) by {
		lemma_eq_ref(temp_130_0);
	}
	let temp_131_0 = (mul_((mod_((mul_(c, b)), m)), (sub_(a, b))));
	let temp_131_1 = (mul_((sub_(a, b)), (mod_((mul_(c, b)), m))));
	assert(eq_(temp_131_0, temp_131_1)) by {
		lemma_mul_comm(mod_(mul_(c, b), m), sub_(a, b));
	}
	let temp_132_0 = (mul_((add_(d, b)), (sub_(a, c))));
	let temp_132_1 = (mul_((sub_(a, c)), (add_(d, b))));
	assert(eq_(temp_132_0, temp_132_1)) by {
		lemma_mul_comm(add_(d, b), sub_(a, c));
	}
	let temp_133_0 = (mul_((mul_(c, c)), (mul_(b, (mod_(b, m))))));
	let temp_133_1 = (mul_((mul_(c, c)), (mul_(b, (mod_((add_((mul_((sub_((add_(c, b)), (mul_(c, b)))), m)), b)), m))))));
	assert(eq_(temp_133_0, temp_133_1)) by {
		lemma_mul_comm(c, c);
		lemma_mod_mul_vanish(b, sub_(add_(c, b), mul_(c, b)), m);
		cong_mul_(mul_(c, c), mul_(b, mod_(b, m)), mul_(c, c), mul_(b, mod_(add_(mul_(sub_(add_(c, b), mul_(c, b)), m), b), m)));
		lemma_eq_ref(b);
		cong_mul_(b, mod_(b, m), b, mod_(add_(mul_(sub_(add_(c, b), mul_(c, b)), m), b), m));
	}
	let temp_134_0 = (mul_((mul_(a, a)), (mul_(a, c))));
	let temp_134_1 = (mul_((mul_((mul_(a, a)), a)), c));
	assert(eq_(temp_134_0, temp_134_1)) by {
		lemma_mul_assoc(mul_(a, a), a, c);
	}
	let temp_135_0 = (add_((mul_(c, a)), (mul_(c, d))));
	let temp_135_1 = (mul_(c, (add_(a, d))));
	assert(eq_(temp_135_0, temp_135_1)) by {
		lemma_eq_sym(temp_135_1, temp_135_0);
		lemma_mul_dist(c, a, d);
	}
	let temp_136_0 = (mod_((add_((mul_(d, b)), (mul_(c, c)))), m));
	let temp_136_1 = (mod_((add_((mod_((mul_(d, b)), m)), (mod_((mul_(c, c)), m)))), m));
	assert(eq_(temp_136_0, temp_136_1)) by {
		lemma_mod_add_noop(mul_(d, b), mul_(c, c), m);
	}
	let temp_137_0 = (mul_((mul_(d, d)), (mul_(b, (mod_(b, m))))));
	let temp_137_1 = (mul_((mul_(d, d)), (mul_(b, (mod_((add_((mul_((mul_((mul_(d, d)), (mul_(c, d)))), m)), b)), m))))));
	assert(eq_(temp_137_0, temp_137_1)) by {
		cong_mul_(b, mod_(b, m), b, mod_(add_(mul_(mul_(mul_(d, d), mul_(c, d)), m), b), m));
		lemma_eq_ref(b);
		lemma_mul_comm(d, d);
		lemma_mod_mul_vanish(b, mul_(mul_(d, d), mul_(c, d)), m);
		cong_mul_(mul_(d, d), mul_(b, mod_(b, m)), mul_(d, d), mul_(b, mod_(add_(mul_(mul_(mul_(d, d), mul_(c, d)), m), b), m)));
	}
	let temp_138_0 = (mul_((mul_(b, d)), (mul_(d, c))));
	let temp_138_1 = (mul_(b, (mul_(d, (mul_(d, c))))));
	assert(eq_(temp_138_0, temp_138_1)) by {
		lemma_eq_sym(temp_138_1, temp_138_0);
		lemma_mul_assoc(b, d, mul_(d, c));
	}
	let temp_139_0 = (mod_((mul_((mul_(as_elem(14), c)), (mul_(a, c)))), m));
	let temp_139_1 = (mod_((add_((mul_((mul_(as_elem(14), c)), (mul_(a, c)))), (mul_((mul_((mul_(c, b)), (add_(b, b)))), m)))), m));
	assert(eq_(temp_139_0, temp_139_1)) by {
		lemma_mod_mul_vanish(mul_(mul_(as_elem(14), c), mul_(a, c)), mul_(mul_(c, b), add_(b, b)), m);
	}
	let temp_140_0 = (mul_((add_(c, c)), (mul_(a, c))));
	let temp_140_1 = (mul_((mul_((add_(c, c)), a)), c));
	assert(eq_(temp_140_0, temp_140_1)) by {
		lemma_mul_assoc(add_(c, c), a, c);
	}
	let temp_141_0 = (mul_((mul_(c, a)), (mul_(b, d))));
	let temp_141_1 = (mul_((mul_(b, d)), (mul_(c, a))));
	assert(eq_(temp_141_0, temp_141_1)) by {
		lemma_mul_comm(mul_(c, a), mul_(b, d));
	}
	let temp_142_0 = (add_((mod_((mul_(a, c)), m)), (mul_(a, c))));
	let temp_142_1 = (add_((mod_((add_((mul_(a, c)), (mul_((mul_((mod_((mul_(d, (mod_(a, m)))), m)), (mul_(a, c)))), m)))), m)), (mul_(a, c))));
	assert(eq_(temp_142_0, temp_142_1)) by {
		lemma_mod_mul_vanish(mul_(a, c), mul_(mod_(mul_(d, mod_(a, m)), m), mul_(a, c)), m);
		cong_add_(mod_(mul_(a, c), m), mul_(a, c), mod_(add_(mul_(a, c), mul_(mul_(mod_(mul_(d, mod_(a, m)), m), mul_(a, c)), m)), m), mul_(a, c));
		lemma_eq_ref(mul_(a, c));
	}
	let temp_143_0 = (mul_((mul_((mod_(a, m)), d)), (mul_(b, b))));
	let temp_143_1 = (mul_((mul_((mod_((add_((mul_((sub_((mod_((add_(d, d)), m)), (mul_(b, d)))), m)), a)), m)), d)), (mul_(b, b))));
	assert(eq_(temp_143_0, temp_143_1)) by {
		lemma_mul_comm(b, b);
		lemma_mod_mul_vanish(a, sub_(mod_(add_(d, d), m), mul_(b, d)), m);
		cong_mul_(mul_(mod_(a, m), d), mul_(b, b), mul_(mod_(add_(mul_(sub_(mod_(add_(d, d), m), mul_(b, d)), m), a), m), d), mul_(b, b));
		lemma_eq_ref(d);
		cong_mul_(mod_(a, m), d, mod_(add_(mul_(sub_(mod_(add_(d, d), m), mul_(b, d)), m), a), m), d);
	}
	let temp_144_0 = (add_((mod_((mul_(a, as_elem(80))), m)), (mul_(as_elem(42), a))));
	let temp_144_1 = (add_((mod_((mul_(a, as_elem(80))), m)), (mul_(a, as_elem(42)))));
	assert(eq_(temp_144_0, temp_144_1)) by {
		lemma_mul_comm(as_elem(42), a);
		cong_add_(mod_(mul_(a, as_elem(80)), m), mul_(as_elem(42), a), mod_(mul_(a, as_elem(80)), m), mul_(a, as_elem(42)));
		lemma_eq_ref(mod_(mul_(a, as_elem(80)), m));
	}
	let temp_145_0 = (mul_((mul_(b, d)), (mul_(b, (mod_(c, m))))));
	let temp_145_1 = (mul_((mul_(b, d)), (mul_(b, (mod_((add_((mul_((mul_((sub_(c, d)), (mod_((mul_(a, c)), m)))), m)), c)), m))))));
	assert(eq_(temp_145_0, temp_145_1)) by {
		lemma_eq_ref(mul_(b, d));
		cong_mul_(b, mod_(c, m), b, mod_(add_(mul_(mul_(sub_(c, d), mod_(mul_(a, c), m)), m), c), m));
		lemma_eq_ref(b);
		lemma_mod_mul_vanish(c, mul_(sub_(c, d), mod_(mul_(a, c), m)), m);
		cong_mul_(mul_(b, d), mul_(b, mod_(c, m)), mul_(b, d), mul_(b, mod_(add_(mul_(mul_(sub_(c, d), mod_(mul_(a, c), m)), m), c), m)));
	}
	let temp_146_0 = (mul_((sub_(c, a)), (mul_(c, a))));
	let temp_146_1 = (mul_((sub_(c, a)), (mul_(a, c))));
	assert(eq_(temp_146_0, temp_146_1)) by {
		cong_mul_(sub_(c, a), mul_(c, a), sub_(c, a), mul_(a, c));
		lemma_mul_comm(c, a);
		lemma_eq_ref(sub_(c, a));
	}
	let temp_147_0 = (mul_((mul_((mod_(a, m)), b)), (mul_(d, b))));
	let temp_147_1 = (mul_((mul_(b, (mod_(a, m)))), (mul_(d, b))));
	assert(eq_(temp_147_0, temp_147_1)) by {
		lemma_mul_comm(mod_(a, m), b);
		cong_mul_(mul_(mod_(a, m), b), mul_(d, b), mul_(b, mod_(a, m)), mul_(d, b));
		lemma_eq_ref(mul_(d, b));
	}
	let temp_148_0 = (mul_((mul_(d, a)), (mul_(c, a))));
	let temp_148_1 = (mul_((mul_(d, a)), (mul_(a, c))));
	assert(eq_(temp_148_0, temp_148_1)) by {
		cong_mul_(mul_(d, a), mul_(c, a), mul_(d, a), mul_(a, c));
		lemma_mul_comm(c, a);
		lemma_eq_ref(mul_(d, a));
	}
	let temp_149_0 = (mod_((sub_((sub_(d, d)), (mul_(b, d)))), m));
	let temp_149_1 = (mod_((add_((mul_((mul_((mul_(as_elem(65), c)), (mul_(b, c)))), m)), (sub_((sub_(d, d)), (mul_(b, d)))))), m));
	assert(eq_(temp_149_0, temp_149_1)) by {
		lemma_mod_mul_vanish(sub_(sub_(d, d), mul_(b, d)), mul_(mul_(as_elem(65), c), mul_(b, c)), m);
	}
	let temp_150_0 = (mul_((mul_(d, c)), (mul_(d, d))));
	let temp_150_1 = (mul_((mul_((mul_(d, c)), d)), d));
	assert(eq_(temp_150_0, temp_150_1)) by {
		lemma_mul_assoc(mul_(d, c), d, d);
	}
	let temp_151_0 = (mul_((mul_(b, d)), (add_(b, a))));
	let temp_151_1 = (add_((mul_((mul_(b, d)), b)), (mul_((mul_(b, d)), a))));
	assert(eq_(temp_151_0, temp_151_1)) by {
		lemma_mul_dist(mul_(b, d), b, a);
	}
	let temp_152_0 = (mod_((add_((sub_(d, b)), (mul_(a, a)))), m));
	let temp_152_1 = (mod_((add_((sub_(d, b)), (mul_(a, a)))), m));
	assert(eq_(temp_152_0, temp_152_1)) by {
		lemma_eq_ref(temp_152_0);
	}
	let temp_153_0 = (mod_((mul_((mul_(a, a)), (add_(c, c)))), m));
	let temp_153_1 = (mod_((mul_((mul_(a, a)), (add_(c, c)))), m));
	assert(eq_(temp_153_0, temp_153_1)) by {
		lemma_eq_ref(temp_153_0);
	}
	let temp_154_0 = (sub_((mul_(d, b)), (mul_(as_elem(52), a))));
	let temp_154_1 = (sub_((mul_(b, d)), (mul_(as_elem(52), a))));
	assert(eq_(temp_154_0, temp_154_1)) by {
		lemma_mul_comm(d, b);
		cong_sub_(mul_(d, b), mul_(as_elem(52), a), mul_(b, d), mul_(as_elem(52), a));
		lemma_eq_ref(mul_(as_elem(52), a));
	}
	let temp_155_0 = (mul_((mod_((mul_(b, b)), m)), (mul_(d, d))));
	let temp_155_1 = (mul_((mod_((sub_((mul_(b, b)), (mul_((mul_((sub_((mod_(c, m)), b)), (mul_(a, d)))), m)))), m)), (mul_(d, d))));
	assert(eq_(temp_155_0, temp_155_1)) by {
		lemma_mul_comm(d, d);
		lemma_mod_mul_vanish(mul_(b, b), mul_(sub_(mod_(c, m), b), mul_(a, d)), m);
		cong_mul_(mod_(mul_(b, b), m), mul_(d, d), mod_(sub_(mul_(b, b), mul_(mul_(sub_(mod_(c, m), b), mul_(a, d)), m)), m), mul_(d, d));
	}
	let temp_156_0 = (mul_((mul_(d, c)), (mul_(b, a))));
	let temp_156_1 = (mul_((mul_(b, a)), (mul_(d, c))));
	assert(eq_(temp_156_0, temp_156_1)) by {
		lemma_mul_comm(mul_(d, c), mul_(b, a));
	}
	let temp_157_0 = (mul_(a, (mul_(d, c))));
	let temp_157_1 = (mul_(a, (mul_(c, d))));
	assert(eq_(temp_157_0, temp_157_1)) by {
		lemma_eq_ref(a);
		cong_mul_(a, mul_(d, c), a, mul_(c, d));
		lemma_mul_comm(d, c);
	}
	let temp_158_0 = (add_((mul_(c, a)), (add_(a, (mod_(c, m))))));
	let temp_158_1 = (add_((mul_(c, a)), (add_((mod_(c, m)), a))));
	assert(eq_(temp_158_0, temp_158_1)) by {
		lemma_add_comm(a, mod_(c, m));
		cong_add_(mul_(c, a), add_(a, mod_(c, m)), mul_(c, a), add_(mod_(c, m), a));
		lemma_eq_ref(mul_(c, a));
	}
	let temp_159_0 = (mul_((mod_((sub_(d, as_elem(66))), m)), (sub_(c, a))));
	let temp_159_1 = (mul_((mod_((add_((mul_((mul_((mul_(d, c)), (mul_(b, d)))), m)), (sub_(d, as_elem(66))))), m)), (sub_(c, a))));
	assert(eq_(temp_159_0, temp_159_1)) by {
		lemma_mod_mul_vanish(sub_(d, as_elem(66)), mul_(mul_(d, c), mul_(b, d)), m);
		cong_mul_(mod_(sub_(d, as_elem(66)), m), sub_(c, a), mod_(add_(mul_(mul_(mul_(d, c), mul_(b, d)), m), sub_(d, as_elem(66))), m), sub_(c, a));
		lemma_eq_ref(sub_(c, a));
	}
	let temp_160_0 = (mul_((mul_(d, d)), (mul_(b, d))));
	let temp_160_1 = (mul_((mul_(b, d)), (mul_(d, d))));
	assert(eq_(temp_160_0, temp_160_1)) by {
		lemma_mul_comm(mul_(d, d), mul_(b, d));
	}
	let temp_161_0 = (mul_((mul_(a, b)), (mul_(d, (mod_(d, m))))));
	let temp_161_1 = (mul_((mul_(d, (mod_(d, m)))), (mul_(a, b))));
	assert(eq_(temp_161_0, temp_161_1)) by {
		lemma_mul_comm(mul_(a, b), mul_(d, mod_(d, m)));
	}
	let temp_162_0 = (mul_((mod_((mul_((mod_(c, m)), (mod_(d, m)))), m)), (mul_(a, as_elem(92)))));
	let temp_162_1 = (mul_((mul_((mod_((mul_((mod_(c, m)), (mod_(d, m)))), m)), a)), as_elem(92)));
	assert(eq_(temp_162_0, temp_162_1)) by {
		lemma_mul_assoc(mod_(mul_(mod_(c, m), mod_(d, m)), m), a, as_elem(92));
	}

}

} // verus!