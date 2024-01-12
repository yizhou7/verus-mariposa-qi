use builtin_macros::*;
// use builtin::*;
mod nl_basics;
use crate::nl_basics::*;
verus! {

pub proof fn free_0(a: Elem, b: Elem, c: Elem, d: Elem, m: Elem)
{
	let temp_0_0 = (mul_((mod_((mul_(c, d)), m)), a));
	let temp_0_1 = (mul_((mod_((mul_(d, c)), m)), a));
	assert(eq_(temp_0_0, temp_0_1)) by {
		lemma_mul_comm(c, d);
		cong_mul_(mod_(mul_(c, d), m), a, mod_(mul_(d, c), m), a);
		cong_mod_(mul_(c, d), m, mul_(d, c), m);
		lemma_eq_ref(a);
		lemma_eq_ref(m);
	}
	let temp_1_0 = (mul_((mul_(b, c)), (mul_(a, b))));
	let temp_1_1 = (mul_((mul_(a, b)), (mul_(b, c))));
	assert(eq_(temp_1_0, temp_1_1)) by {
		lemma_mul_comm(mul_(b, c), mul_(a, b));
	}
	let temp_2_0 = (mul_((add_(a, c)), (mul_(b, b))));
	let temp_2_1 = (add_((mul_(a, (mul_(b, b)))), (mul_(c, (mul_(b, b))))));
	assert(eq_(temp_2_0, temp_2_1)) by {
		lemma_mul_dist(a, c, mul_(b, b));
	}
	let temp_3_0 = (mul_((mul_(c, a)), (mul_(b, a))));
	let temp_3_1 = (mul_(c, (mul_(a, (mul_(b, a))))));
	assert(eq_(temp_3_0, temp_3_1)) by {
		lemma_eq_sym(temp_3_1, temp_3_0);
		lemma_mul_assoc(c, a, mul_(b, a));
	}
	let temp_4_0 = (mod_((add_((mod_((add_(d, b)), m)), (mul_(a, a)))), m));
	let temp_4_1 = (mod_((add_((mod_((add_(d, b)), m)), (mul_(a, a)))), m));
	assert(eq_(temp_4_0, temp_4_1)) by {
		lemma_eq_ref(temp_4_0);
	}
	let temp_5_0 = (mul_((mul_(b, d)), (mul_(d, c))));
	let temp_5_1 = (mul_((mul_(d, b)), (mul_(d, c))));
	assert(eq_(temp_5_0, temp_5_1)) by {
		cong_mul_(mul_(b, d), mul_(d, c), mul_(d, b), mul_(d, c));
		lemma_mul_comm(b, d);
		lemma_eq_ref(mul_(d, c));
	}
	let temp_6_0 = (mul_((mod_((mul_(a, (mod_(a, m)))), m)), (mul_((mod_(c, m)), a))));
	let temp_6_1 = (mul_((mod_((mod_((mul_(a, a)), m)), m)), (mul_((mod_(c, m)), a))));
	assert(eq_(temp_6_0, temp_6_1)) by {
		lemma_eq_ref(mul_(mod_(c, m), a));
		lemma_eq_sym(mod_(mod_(mul_(a, a), m), m), mod_(mul_(a, mod_(a, m)), m));
		lemma_mod_mul_noop(a, a, m);
		cong_mul_(mod_(mul_(a, mod_(a, m)), m), mul_(mod_(c, m), a), mod_(mod_(mul_(a, a), m), m), mul_(mod_(c, m), a));
	}
	let temp_7_0 = (mul_((mod_((mul_(c, a)), m)), (add_(b, c))));
	let temp_7_1 = (mul_((mod_((sub_((mul_(c, a)), (mul_((mul_((mod_((sub_((mod_(b, m)), b)), m)), (mul_(b, d)))), m)))), m)), (add_(b, c))));
	assert(eq_(temp_7_0, temp_7_1)) by {
		lemma_mod_mul_vanish(mul_(c, a), mul_(mod_(sub_(mod_(b, m), b), m), mul_(b, d)), m);
		cong_mul_(mod_(mul_(c, a), m), add_(b, c), mod_(sub_(mul_(c, a), mul_(mul_(mod_(sub_(mod_(b, m), b), m), mul_(b, d)), m)), m), add_(b, c));
		lemma_eq_ref(add_(b, c));
	}
	let temp_8_0 = (mul_((mul_(d, (mod_(c, m)))), (mul_(c, d))));
	let temp_8_1 = (mul_((mul_(c, d)), (mul_(d, (mod_(c, m))))));
	assert(eq_(temp_8_0, temp_8_1)) by {
		lemma_mul_comm(mul_(d, mod_(c, m)), mul_(c, d));
	}
	let temp_9_0 = (mul_((mul_(c, (mod_(b, m)))), (mul_(c, d))));
	let temp_9_1 = (mul_((mul_(c, (mod_((add_(b, (mul_((mod_((mul_((mul_((mod_(a, m)), c)), (mod_((add_(a, (mod_(d, m)))), m)))), m)), m)))), m)))), (mul_(c, d))));
	assert(eq_(temp_9_0, temp_9_1)) by {
		lemma_eq_ref(mul_(c, d));
		cong_mul_(mul_(c, mod_(b, m)), mul_(c, d), mul_(c, mod_(add_(b, mul_(mod_(mul_(mul_(mod_(a, m), c), mod_(add_(a, mod_(d, m)), m)), m), m)), m)), mul_(c, d));
		lemma_mod_mul_vanish(b, mod_(mul_(mul_(mod_(a, m), c), mod_(add_(a, mod_(d, m)), m)), m), m);
		cong_mul_(c, mod_(b, m), c, mod_(add_(b, mul_(mod_(mul_(mul_(mod_(a, m), c), mod_(add_(a, mod_(d, m)), m)), m), m)), m));
		lemma_eq_ref(c);
	}
	let temp_10_0 = (mul_((mod_((mul_(a, a)), m)), (mul_(d, b))));
	let temp_10_1 = (mul_((mul_((mod_((mul_(a, a)), m)), d)), b));
	assert(eq_(temp_10_0, temp_10_1)) by {
		lemma_mul_assoc(mod_(mul_(a, a), m), d, b);
	}
	let temp_11_0 = (mul_((mul_(a, d)), (mul_(b, a))));
	let temp_11_1 = (mul_((mul_((mul_(a, d)), b)), a));
	assert(eq_(temp_11_0, temp_11_1)) by {
		lemma_mul_assoc(mul_(a, d), b, a);
	}
	let temp_12_0 = (mul_((mul_((mod_(a, m)), a)), (sub_(a, b))));
	let temp_12_1 = (mul_((mul_(a, (mod_(a, m)))), (sub_(a, b))));
	assert(eq_(temp_12_0, temp_12_1)) by {
		cong_mul_(mul_(mod_(a, m), a), sub_(a, b), mul_(a, mod_(a, m)), sub_(a, b));
		lemma_mul_comm(mod_(a, m), a);
		lemma_eq_ref(sub_(a, b));
	}
	let temp_13_0 = (mul_((mul_(d, b)), (mod_((mul_(d, d)), m))));
	let temp_13_1 = (mul_(d, (mul_(b, (mod_((mul_(d, d)), m))))));
	assert(eq_(temp_13_0, temp_13_1)) by {
		lemma_eq_sym(temp_13_1, temp_13_0);
		lemma_mul_assoc(d, b, mod_(mul_(d, d), m));
	}
	let temp_14_0 = (mul_((mod_((mul_(c, d)), m)), (mul_(d, c))));
	let temp_14_1 = (mul_((mod_((add_((mul_((mod_((mul_((mul_(b, d)), (mul_(c, (mod_(c, m)))))), m)), m)), (mul_(c, d)))), m)), (mul_(d, c))));
	assert(eq_(temp_14_0, temp_14_1)) by {
		lemma_mod_mul_vanish(mul_(c, d), mod_(mul_(mul_(b, d), mul_(c, mod_(c, m))), m), m);
		cong_mul_(mod_(mul_(c, d), m), mul_(d, c), mod_(add_(mul_(mod_(mul_(mul_(b, d), mul_(c, mod_(c, m))), m), m), mul_(c, d)), m), mul_(d, c));
		lemma_eq_ref(mul_(d, c));
	}
	let temp_15_0 = (mod_((mul_((mul_(c, a)), (mod_((mul_(b, c)), m)))), m));
	let temp_15_1 = (mod_((mul_((mul_(c, a)), (mod_((mul_(c, b)), m)))), m));
	assert(eq_(temp_15_0, temp_15_1)) by {
		lemma_mul_comm(b, c);
		cong_mod_(mul_(mul_(c, a), mod_(mul_(b, c), m)), m, mul_(mul_(c, a), mod_(mul_(c, b), m)), m);
		cong_mul_(mul_(c, a), mod_(mul_(b, c), m), mul_(c, a), mod_(mul_(c, b), m));
		lemma_eq_ref(m);
		lemma_eq_ref(mul_(c, a));
		cong_mod_(mul_(b, c), m, mul_(c, b), m);
	}
	let temp_16_0 = (mul_((sub_(c, b)), (mul_((mod_(a, m)), c))));
	let temp_16_1 = (mul_((sub_(c, b)), (mul_((mod_((add_((mul_((mod_((add_((mul_(b, c)), (mod_((mul_(d, c)), m)))), m)), m)), a)), m)), c))));
	assert(eq_(temp_16_0, temp_16_1)) by {
		lemma_mod_mul_vanish(a, mod_(add_(mul_(b, c), mod_(mul_(d, c), m)), m), m);
		cong_mul_(sub_(c, b), mul_(mod_(a, m), c), sub_(c, b), mul_(mod_(add_(mul_(mod_(add_(mul_(b, c), mod_(mul_(d, c), m)), m), m), a), m), c));
		lemma_eq_ref(c);
		cong_mul_(mod_(a, m), c, mod_(add_(mul_(mod_(add_(mul_(b, c), mod_(mul_(d, c), m)), m), m), a), m), c);
		lemma_eq_ref(sub_(c, b));
	}
	let temp_17_0 = (mul_((mul_(c, (mod_(a, m)))), (mul_(a, c))));
	let temp_17_1 = (mul_((mul_(a, c)), (mul_(c, (mod_(a, m))))));
	assert(eq_(temp_17_0, temp_17_1)) by {
		lemma_mul_comm(mul_(c, mod_(a, m)), mul_(a, c));
	}
	let temp_18_0 = (mod_((add_((mul_(b, b)), (add_((mod_(a, m)), d)))), m));
	let temp_18_1 = (mod_((add_((mul_(b, b)), (add_((mod_(a, m)), d)))), m));
	assert(eq_(temp_18_0, temp_18_1)) by {
		lemma_eq_ref(temp_18_0);
	}
	let temp_19_0 = (add_((mul_(c, d)), (mul_(b, a))));
	let temp_19_1 = (add_((mul_(c, d)), (mul_(a, b))));
	assert(eq_(temp_19_0, temp_19_1)) by {
		cong_add_(mul_(c, d), mul_(b, a), mul_(c, d), mul_(a, b));
		lemma_mul_comm(b, a);
		lemma_eq_ref(mul_(c, d));
	}
	let temp_20_0 = (mul_((sub_(b, d)), (add_(d, b))));
	let temp_20_1 = (mul_((add_(d, b)), (sub_(b, d))));
	assert(eq_(temp_20_0, temp_20_1)) by {
		lemma_mul_comm(sub_(b, d), add_(d, b));
	}
	let temp_21_0 = (mul_((mul_(b, a)), (mul_(c, b))));
	let temp_21_1 = (mul_((mul_(b, a)), (mul_(b, c))));
	assert(eq_(temp_21_0, temp_21_1)) by {
		cong_mul_(mul_(b, a), mul_(c, b), mul_(b, a), mul_(b, c));
		lemma_mul_comm(c, b);
		lemma_eq_ref(mul_(b, a));
	}
	let temp_22_0 = (add_((mul_(a, c)), (sub_(c, a))));
	let temp_22_1 = (add_((sub_(c, a)), (mul_(a, c))));
	assert(eq_(temp_22_0, temp_22_1)) by {
		lemma_add_comm(mul_(a, c), sub_(c, a));
	}
	let temp_23_0 = (add_((mul_(d, d)), (mul_(c, a))));
	let temp_23_1 = (add_((mul_(d, d)), (mul_(c, a))));
	assert(eq_(temp_23_0, temp_23_1)) by {
		lemma_eq_ref(temp_23_0);
	}
	let temp_24_0 = (mod_((mul_((mod_((mul_(a, (mod_(as_elem(37), m)))), m)), (mul_(a, a)))), m));
	let temp_24_1 = (mod_((mul_((mod_((mul_(a, (mod_(as_elem(37), m)))), m)), (mul_(a, a)))), m));
	assert(eq_(temp_24_0, temp_24_1)) by {
		lemma_eq_ref(temp_24_0);
	}
	let temp_25_0 = (mul_((mul_(b, b)), (mul_(a, c))));
	let temp_25_1 = (mul_(b, (mul_(b, (mul_(a, c))))));
	assert(eq_(temp_25_0, temp_25_1)) by {
		lemma_eq_sym(temp_25_1, temp_25_0);
		lemma_mul_assoc(b, b, mul_(a, c));
	}
	let temp_26_0 = (mul_((mul_((mod_(b, m)), b)), (mul_(c, c))));
	let temp_26_1 = (mul_((mul_(b, (mod_(b, m)))), (mul_(c, c))));
	assert(eq_(temp_26_0, temp_26_1)) by {
		cong_mul_(mul_(mod_(b, m), b), mul_(c, c), mul_(b, mod_(b, m)), mul_(c, c));
		lemma_mul_comm(mod_(b, m), b);
		lemma_eq_ref(mul_(c, c));
	}
	let temp_27_0 = (mul_((sub_(a, a)), (mul_(d, c))));
	let temp_27_1 = (mul_((mul_((sub_(a, a)), d)), c));
	assert(eq_(temp_27_0, temp_27_1)) by {
		lemma_mul_assoc(sub_(a, a), d, c);
	}
	let temp_28_0 = (sub_((mul_(a, b)), c));
	let temp_28_1 = (sub_((mul_(b, a)), c));
	assert(eq_(temp_28_0, temp_28_1)) by {
		cong_sub_(mul_(a, b), c, mul_(b, a), c);
		lemma_mul_comm(a, b);
		lemma_eq_ref(c);
	}
	let temp_29_0 = (sub_((mul_(c, a)), (mod_((add_(d, a)), m))));
	let temp_29_1 = (sub_((mul_(c, a)), (mod_((add_((add_(d, a)), (mul_((mul_((mul_(a, d)), (mul_(c, c)))), m)))), m))));
	assert(eq_(temp_29_0, temp_29_1)) by {
		lemma_mod_mul_vanish(add_(d, a), mul_(mul_(a, d), mul_(c, c)), m);
		cong_sub_(mul_(c, a), mod_(add_(d, a), m), mul_(c, a), mod_(add_(add_(d, a), mul_(mul_(mul_(a, d), mul_(c, c)), m)), m));
		lemma_eq_ref(mul_(c, a));
	}
	let temp_30_0 = (mul_((mul_(as_elem(16), d)), (mul_((mod_(d, m)), a))));
	let temp_30_1 = (mul_((mul_(as_elem(16), d)), (mul_((mod_((sub_(d, (mul_((add_((mul_(d, (mod_(c, m)))), (mul_(b, c)))), m)))), m)), a))));
	assert(eq_(temp_30_0, temp_30_1)) by {
		lemma_mod_mul_vanish(d, add_(mul_(d, mod_(c, m)), mul_(b, c)), m);
		cong_mul_(mul_(as_elem(16), d), mul_(mod_(d, m), a), mul_(as_elem(16), d), mul_(mod_(sub_(d, mul_(add_(mul_(d, mod_(c, m)), mul_(b, c)), m)), m), a));
		lemma_eq_ref(mul_(as_elem(16), d));
		cong_mul_(mod_(d, m), a, mod_(sub_(d, mul_(add_(mul_(d, mod_(c, m)), mul_(b, c)), m)), m), a);
		lemma_eq_ref(a);
	}
	let temp_31_0 = (mul_((add_((mod_(d, m)), d)), (mul_(a, c))));
	let temp_31_1 = (mul_((add_((mod_((add_(d, (mul_((mul_((mod_((mul_((mod_(c, m)), a)), m)), (sub_(b, a)))), m)))), m)), d)), (mul_(a, c))));
	assert(eq_(temp_31_0, temp_31_1)) by {
		lemma_mod_mul_vanish(d, mul_(mod_(mul_(mod_(c, m), a), m), sub_(b, a)), m);
		cong_mul_(add_(mod_(d, m), d), mul_(a, c), add_(mod_(add_(d, mul_(mul_(mod_(mul_(mod_(c, m), a), m), sub_(b, a)), m)), m), d), mul_(a, c));
		cong_add_(mod_(d, m), d, mod_(add_(d, mul_(mul_(mod_(mul_(mod_(c, m), a), m), sub_(b, a)), m)), m), d);
		lemma_eq_ref(mul_(a, c));
		lemma_eq_ref(d);
	}
	let temp_32_0 = (mod_((mul_((mul_(b, (mod_(d, m)))), (mul_(c, c)))), m));
	let temp_32_1 = (mod_((mul_((mul_(b, (mod_((sub_(d, (mul_((add_((mod_((mul_(d, b)), m)), (mul_(a, d)))), m)))), m)))), (mul_(c, c)))), m));
	assert(eq_(temp_32_0, temp_32_1)) by {
		lemma_mul_comm(c, c);
		lemma_mod_mul_vanish(d, add_(mod_(mul_(d, b), m), mul_(a, d)), m);
		cong_mod_(mul_(mul_(b, mod_(d, m)), mul_(c, c)), m, mul_(mul_(b, mod_(sub_(d, mul_(add_(mod_(mul_(d, b), m), mul_(a, d)), m)), m)), mul_(c, c)), m);
		lemma_eq_ref(b);
		cong_mul_(mul_(b, mod_(d, m)), mul_(c, c), mul_(b, mod_(sub_(d, mul_(add_(mod_(mul_(d, b), m), mul_(a, d)), m)), m)), mul_(c, c));
		lemma_eq_ref(m);
		cong_mul_(b, mod_(d, m), b, mod_(sub_(d, mul_(add_(mod_(mul_(d, b), m), mul_(a, d)), m)), m));
	}
	let temp_33_0 = (mul_((mod_((mul_((mod_(a, m)), d)), m)), (mul_(c, b))));
	let temp_33_1 = (mul_((mod_((add_((mul_((mod_(a, m)), d)), (mul_((mul_((mul_(b, a)), (sub_(d, b)))), m)))), m)), (mul_(c, b))));
	assert(eq_(temp_33_0, temp_33_1)) by {
		lemma_mod_mul_vanish(mul_(mod_(a, m), d), mul_(mul_(b, a), sub_(d, b)), m);
		cong_mul_(mod_(mul_(mod_(a, m), d), m), mul_(c, b), mod_(add_(mul_(mod_(a, m), d), mul_(mul_(mul_(b, a), sub_(d, b)), m)), m), mul_(c, b));
		lemma_eq_ref(mul_(c, b));
	}
	let temp_34_0 = (mul_((mul_(as_elem(14), b)), (mul_(b, c))));
	let temp_34_1 = (mul_((mul_(b, as_elem(14))), (mul_(b, c))));
	assert(eq_(temp_34_0, temp_34_1)) by {
		cong_mul_(mul_(as_elem(14), b), mul_(b, c), mul_(b, as_elem(14)), mul_(b, c));
		lemma_mul_comm(as_elem(14), b);
		lemma_eq_ref(mul_(b, c));
	}
	let temp_35_0 = (mul_((mul_((mod_(d, m)), d)), (sub_(b, (mod_(b, m))))));
	let temp_35_1 = (mul_((sub_(b, (mod_(b, m)))), (mul_((mod_(d, m)), d))));
	assert(eq_(temp_35_0, temp_35_1)) by {
		lemma_mul_comm(mul_(mod_(d, m), d), sub_(b, mod_(b, m)));
	}
	let temp_36_0 = (add_((add_(b, as_elem(3))), (mod_((mul_(a, c)), m))));
	let temp_36_1 = (add_((add_(as_elem(3), b)), (mod_((mul_(a, c)), m))));
	assert(eq_(temp_36_0, temp_36_1)) by {
		lemma_add_comm(b, as_elem(3));
		cong_add_(add_(b, as_elem(3)), mod_(mul_(a, c), m), add_(as_elem(3), b), mod_(mul_(a, c), m));
		lemma_eq_ref(mod_(mul_(a, c), m));
	}
	let temp_37_0 = (mul_((mod_((mul_(d, c)), m)), (mul_(b, a))));
	let temp_37_1 = (mul_((mod_((add_((mul_((sub_((mul_(d, c)), (mul_(d, c)))), m)), (mul_(d, c)))), m)), (mul_(b, a))));
	assert(eq_(temp_37_0, temp_37_1)) by {
		lemma_mod_mul_vanish(mul_(d, c), sub_(mul_(d, c), mul_(d, c)), m);
		cong_mul_(mod_(mul_(d, c), m), mul_(b, a), mod_(add_(mul_(sub_(mul_(d, c), mul_(d, c)), m), mul_(d, c)), m), mul_(b, a));
		lemma_eq_ref(mul_(b, a));
	}
	let temp_38_0 = (mul_((mul_(b, d)), (mul_(c, (mod_(a, m))))));
	let temp_38_1 = (mul_(b, (mul_(d, (mul_(c, (mod_(a, m))))))));
	assert(eq_(temp_38_0, temp_38_1)) by {
		lemma_mul_assoc(b, d, mul_(c, mod_(a, m)));
		lemma_eq_sym(temp_38_1, temp_38_0);
	}
	let temp_39_0 = (mul_((sub_(c, c)), (mul_(a, d))));
	let temp_39_1 = (mul_((mul_(a, d)), (sub_(c, c))));
	assert(eq_(temp_39_0, temp_39_1)) by {
		lemma_mul_comm(sub_(c, c), mul_(a, d));
	}
	let temp_40_0 = (mul_((mul_(b, d)), (mul_(a, d))));
	let temp_40_1 = (mul_(b, (mul_(d, (mul_(a, d))))));
	assert(eq_(temp_40_0, temp_40_1)) by {
		lemma_eq_sym(temp_40_1, temp_40_0);
		lemma_mul_assoc(b, d, mul_(a, d));
	}
	let temp_41_0 = (mul_((mul_(b, as_elem(5))), (add_(c, a))));
	let temp_41_1 = (mul_(b, (mul_(as_elem(5), (add_(c, a))))));
	assert(eq_(temp_41_0, temp_41_1)) by {
		lemma_mul_assoc(b, as_elem(5), add_(c, a));
		lemma_eq_sym(temp_41_1, temp_41_0);
	}
	let temp_42_0 = (add_((sub_(d, d)), (mul_(c, as_elem(79)))));
	let temp_42_1 = (add_((mul_(c, as_elem(79))), (sub_(d, d))));
	assert(eq_(temp_42_0, temp_42_1)) by {
		lemma_add_comm(sub_(d, d), mul_(c, as_elem(79)));
	}
	let temp_43_0 = (mul_((mul_(c, b)), (mul_(c, as_elem(97)))));
	let temp_43_1 = (mul_((mul_((mul_(c, b)), c)), as_elem(97)));
	assert(eq_(temp_43_0, temp_43_1)) by {
		lemma_mul_assoc(mul_(c, b), c, as_elem(97));
	}
	let temp_44_0 = (mul_(d, (mul_(b, d))));
	let temp_44_1 = (mul_(d, (mul_(d, b))));
	assert(eq_(temp_44_0, temp_44_1)) by {
		cong_mul_(d, mul_(b, d), d, mul_(d, b));
		lemma_mul_comm(b, d);
		lemma_eq_ref(d);
	}
	let temp_45_0 = (mul_((mul_(c, (mod_(b, m)))), (mul_(c, a))));
	let temp_45_1 = (mul_((mul_((mul_(c, (mod_(b, m)))), c)), a));
	assert(eq_(temp_45_0, temp_45_1)) by {
		lemma_mul_assoc(mul_(c, mod_(b, m)), c, a);
	}
	let temp_46_0 = (mul_((mul_(b, c)), (mul_(a, b))));
	let temp_46_1 = (mul_((mul_(b, c)), (mul_(b, a))));
	assert(eq_(temp_46_0, temp_46_1)) by {
		cong_mul_(mul_(b, c), mul_(a, b), mul_(b, c), mul_(b, a));
		lemma_mul_comm(a, b);
		lemma_eq_ref(mul_(b, c));
	}
	let temp_47_0 = (mul_((mul_(c, b)), (mul_(a, a))));
	let temp_47_1 = (mul_((mul_(b, c)), (mul_(a, a))));
	assert(eq_(temp_47_0, temp_47_1)) by {
		cong_mul_(mul_(c, b), mul_(a, a), mul_(b, c), mul_(a, a));
		lemma_mul_comm(c, b);
		lemma_mul_comm(a, a);
	}
	let temp_48_0 = (mul_((add_(b, c)), (mul_(a, a))));
	let temp_48_1 = (mul_((add_(c, b)), (mul_(a, a))));
	assert(eq_(temp_48_0, temp_48_1)) by {
		cong_mul_(add_(b, c), mul_(a, a), add_(c, b), mul_(a, a));
		lemma_add_comm(b, c);
		lemma_mul_comm(a, a);
	}
	let temp_49_0 = (mul_((add_(a, c)), (add_(d, b))));
	let temp_49_1 = (add_((mul_(a, (add_(d, b)))), (mul_(c, (add_(d, b))))));
	assert(eq_(temp_49_0, temp_49_1)) by {
		lemma_mul_dist(a, c, add_(d, b));
	}
	let temp_50_0 = (mul_((mul_(a, a)), (mod_((mul_(b, a)), m))));
	let temp_50_1 = (mul_((mul_(a, a)), (mod_((sub_((mul_(b, a)), (mul_((mul_((mul_(b, c)), (mul_(b, (mod_(d, m)))))), m)))), m))));
	assert(eq_(temp_50_0, temp_50_1)) by {
		lemma_mul_comm(a, a);
		lemma_mod_mul_vanish(mul_(b, a), mul_(mul_(b, c), mul_(b, mod_(d, m))), m);
		cong_mul_(mul_(a, a), mod_(mul_(b, a), m), mul_(a, a), mod_(sub_(mul_(b, a), mul_(mul_(mul_(b, c), mul_(b, mod_(d, m))), m)), m));
	}
	let temp_51_0 = (sub_((add_(c, as_elem(49))), (mul_(b, c))));
	let temp_51_1 = (sub_((add_(c, as_elem(49))), (mul_(c, b))));
	assert(eq_(temp_51_0, temp_51_1)) by {
		cong_sub_(add_(c, as_elem(49)), mul_(b, c), add_(c, as_elem(49)), mul_(c, b));
		lemma_mul_comm(b, c);
		lemma_eq_ref(add_(c, as_elem(49)));
	}
	let temp_52_0 = (sub_((mod_((sub_(a, c)), m)), (sub_((mod_(b, m)), b))));
	let temp_52_1 = (sub_((mod_((add_((mul_((mul_((sub_(d, d)), (mul_(a, c)))), m)), (sub_(a, c)))), m)), (sub_((mod_(b, m)), b))));
	assert(eq_(temp_52_0, temp_52_1)) by {
		lemma_mod_mul_vanish(sub_(a, c), mul_(sub_(d, d), mul_(a, c)), m);
		cong_sub_(mod_(sub_(a, c), m), sub_(mod_(b, m), b), mod_(add_(mul_(mul_(sub_(d, d), mul_(a, c)), m), sub_(a, c)), m), sub_(mod_(b, m), b));
		lemma_eq_ref(sub_(mod_(b, m), b));
	}
	let temp_53_0 = (mul_((mul_((mod_(d, m)), d)), (mul_(c, a))));
	let temp_53_1 = (mul_((mul_(c, a)), (mul_((mod_(d, m)), d))));
	assert(eq_(temp_53_0, temp_53_1)) by {
		lemma_mul_comm(mul_(mod_(d, m), d), mul_(c, a));
	}
	let temp_54_0 = (mul_((mul_(d, c)), (mul_(b, b))));
	let temp_54_1 = (mul_(d, (mul_(c, (mul_(b, b))))));
	assert(eq_(temp_54_0, temp_54_1)) by {
		lemma_eq_sym(temp_54_1, temp_54_0);
		lemma_mul_assoc(d, c, mul_(b, b));
	}
	let temp_55_0 = (mod_((mul_((mul_(b, c)), (mul_(b, (mod_(a, m)))))), m));
	let temp_55_1 = (mod_((sub_((mul_((mul_(b, c)), (mul_(b, (mod_(a, m)))))), (mul_((mod_((mul_((sub_(c, a)), (mul_(a, d)))), m)), m)))), m));
	assert(eq_(temp_55_0, temp_55_1)) by {
		lemma_mod_mul_vanish(mul_(mul_(b, c), mul_(b, mod_(a, m))), mod_(mul_(sub_(c, a), mul_(a, d)), m), m);
	}
	let temp_56_0 = (mul_((add_(c, b)), (mul_(d, (mod_(c, m))))));
	let temp_56_1 = (mul_((add_(b, c)), (mul_(d, (mod_(c, m))))));
	assert(eq_(temp_56_0, temp_56_1)) by {
		lemma_add_comm(c, b);
		cong_mul_(add_(c, b), mul_(d, mod_(c, m)), add_(b, c), mul_(d, mod_(c, m)));
		lemma_eq_ref(mul_(d, mod_(c, m)));
	}
	let temp_57_0 = (mul_((mul_(a, d)), (mul_(d, c))));
	let temp_57_1 = (mul_(a, (mul_(d, (mul_(d, c))))));
	assert(eq_(temp_57_0, temp_57_1)) by {
		lemma_eq_sym(temp_57_1, temp_57_0);
		lemma_mul_assoc(a, d, mul_(d, c));
	}
	let temp_58_0 = (mul_((mul_(b, d)), (sub_(b, c))));
	let temp_58_1 = (mul_(b, (mul_(d, (sub_(b, c))))));
	assert(eq_(temp_58_0, temp_58_1)) by {
		lemma_eq_sym(temp_58_1, temp_58_0);
		lemma_mul_assoc(b, d, sub_(b, c));
	}
	let temp_59_0 = (mod_((mul_((mul_(a, (mod_(d, m)))), (mul_(d, (mod_(as_elem(54), m)))))), m));
	let temp_59_1 = (mod_((mul_((mul_(a, (mod_((add_((mul_((mod_((add_((add_(c, d)), (sub_(b, (mod_(c, m)))))), m)), m)), d)), m)))), (mul_(d, (mod_(as_elem(54), m)))))), m));
	assert(eq_(temp_59_0, temp_59_1)) by {
		cong_mod_(mul_(mul_(a, mod_(d, m)), mul_(d, mod_(as_elem(54), m))), m, mul_(mul_(a, mod_(add_(mul_(mod_(add_(add_(c, d), sub_(b, mod_(c, m))), m), m), d), m)), mul_(d, mod_(as_elem(54), m))), m);
		lemma_mod_mul_vanish(d, mod_(add_(add_(c, d), sub_(b, mod_(c, m))), m), m);
		lemma_eq_ref(a);
		lemma_eq_ref(m);
		cong_mul_(mul_(a, mod_(d, m)), mul_(d, mod_(as_elem(54), m)), mul_(a, mod_(add_(mul_(mod_(add_(add_(c, d), sub_(b, mod_(c, m))), m), m), d), m)), mul_(d, mod_(as_elem(54), m)));
		cong_mul_(a, mod_(d, m), a, mod_(add_(mul_(mod_(add_(add_(c, d), sub_(b, mod_(c, m))), m), m), d), m));
		lemma_eq_ref(mul_(d, mod_(as_elem(54), m)));
	}
	let temp_60_0 = (mul_((mul_(a, a)), (mul_(b, b))));
	let temp_60_1 = (mul_((mul_((mul_(a, a)), b)), b));
	assert(eq_(temp_60_0, temp_60_1)) by {
		lemma_mul_assoc(mul_(a, a), b, b);
	}
	let temp_61_0 = (add_((mul_(c, c)), (add_(a, d))));
	let temp_61_1 = (add_((mul_(c, c)), (add_(a, d))));
	assert(eq_(temp_61_0, temp_61_1)) by {
		lemma_eq_ref(temp_61_0);
	}
	let temp_62_0 = (add_((mod_((mul_(b, b)), m)), (mul_(c, d))));
	let temp_62_1 = (add_((mod_((add_((mul_(b, b)), (mul_((mul_((mul_(c, b)), (mul_(d, a)))), m)))), m)), (mul_(c, d))));
	assert(eq_(temp_62_0, temp_62_1)) by {
		lemma_mod_mul_vanish(mul_(b, b), mul_(mul_(c, b), mul_(d, a)), m);
		cong_add_(mod_(mul_(b, b), m), mul_(c, d), mod_(add_(mul_(b, b), mul_(mul_(mul_(c, b), mul_(d, a)), m)), m), mul_(c, d));
		lemma_eq_ref(mul_(c, d));
	}
	let temp_63_0 = (mul_((mul_(d, b)), (mul_((mod_(d, m)), d))));
	let temp_63_1 = (mul_((mul_(b, d)), (mul_((mod_(d, m)), d))));
	assert(eq_(temp_63_0, temp_63_1)) by {
		cong_mul_(mul_(d, b), mul_(mod_(d, m), d), mul_(b, d), mul_(mod_(d, m), d));
		lemma_mul_comm(d, b);
		lemma_eq_ref(mul_(mod_(d, m), d));
	}
	let temp_64_0 = (sub_((mul_(b, c)), (add_(c, c))));
	let temp_64_1 = (sub_((mul_(c, b)), (add_(c, c))));
	assert(eq_(temp_64_0, temp_64_1)) by {
		cong_sub_(mul_(b, c), add_(c, c), mul_(c, b), add_(c, c));
		lemma_add_comm(c, c);
		lemma_mul_comm(b, c);
	}
	let temp_65_0 = (mod_((mul_((sub_(a, c)), (mul_(d, as_elem(3))))), m));
	let temp_65_1 = (mod_((mul_((mul_((sub_(a, c)), d)), as_elem(3))), m));
	assert(eq_(temp_65_0, temp_65_1)) by {
		lemma_mul_assoc(sub_(a, c), d, as_elem(3));
		cong_mod_(mul_(sub_(a, c), mul_(d, as_elem(3))), m, mul_(mul_(sub_(a, c), d), as_elem(3)), m);
		lemma_eq_ref(m);
	}
	let temp_66_0 = (mul_((sub_(c, b)), (add_(d, d))));
	let temp_66_1 = (mul_((add_(d, d)), (sub_(c, b))));
	assert(eq_(temp_66_0, temp_66_1)) by {
		lemma_mul_comm(sub_(c, b), add_(d, d));
	}
	let temp_67_0 = (mul_((mod_((mul_(d, c)), m)), (sub_(as_elem(66), a))));
	let temp_67_1 = (mul_((mod_((sub_((mul_(d, c)), (mul_((mul_((mul_(d, a)), (mul_(c, d)))), m)))), m)), (sub_(as_elem(66), a))));
	assert(eq_(temp_67_0, temp_67_1)) by {
		lemma_mod_mul_vanish(mul_(d, c), mul_(mul_(d, a), mul_(c, d)), m);
		cong_mul_(mod_(mul_(d, c), m), sub_(as_elem(66), a), mod_(sub_(mul_(d, c), mul_(mul_(mul_(d, a), mul_(c, d)), m)), m), sub_(as_elem(66), a));
		lemma_eq_ref(sub_(as_elem(66), a));
	}
	let temp_68_0 = (mul_((sub_(d, a)), (mod_((sub_(c, d)), m))));
	let temp_68_1 = (mul_((mod_((sub_(c, d)), m)), (sub_(d, a))));
	assert(eq_(temp_68_0, temp_68_1)) by {
		lemma_mul_comm(sub_(d, a), mod_(sub_(c, d), m));
	}
	let temp_69_0 = (mul_((mul_(a, a)), (mul_(b, a))));
	let temp_69_1 = (mul_((mul_(b, a)), (mul_(a, a))));
	assert(eq_(temp_69_0, temp_69_1)) by {
		lemma_mul_comm(mul_(a, a), mul_(b, a));
	}
	let temp_70_0 = (mul_((mul_((mod_(c, m)), b)), (mul_(d, d))));
	let temp_70_1 = (mul_((mod_(c, m)), (mul_(b, (mul_(d, d))))));
	assert(eq_(temp_70_0, temp_70_1)) by {
		lemma_mul_assoc(mod_(c, m), b, mul_(d, d));
		lemma_eq_sym(temp_70_1, temp_70_0);
	}
	let temp_71_0 = (sub_((mul_(a, c)), (mod_((mul_((mod_(a, m)), (mod_(d, m)))), m))));
	let temp_71_1 = (sub_((mul_(a, c)), (mod_((add_((mul_((mod_(a, m)), (mod_(d, m)))), (mul_((mul_((mul_(b, c)), (mul_(c, a)))), m)))), m))));
	assert(eq_(temp_71_0, temp_71_1)) by {
		lemma_mod_mul_vanish(mul_(mod_(a, m), mod_(d, m)), mul_(mul_(b, c), mul_(c, a)), m);
		cong_sub_(mul_(a, c), mod_(mul_(mod_(a, m), mod_(d, m)), m), mul_(a, c), mod_(add_(mul_(mod_(a, m), mod_(d, m)), mul_(mul_(mul_(b, c), mul_(c, a)), m)), m));
		lemma_eq_ref(mul_(a, c));
	}
	let temp_72_0 = (mod_((sub_((mul_(b, (mod_(a, m)))), (mul_(b, a)))), m));
	let temp_72_1 = (mod_((sub_((mul_((mod_(a, m)), b)), (mul_(b, a)))), m));
	assert(eq_(temp_72_0, temp_72_1)) by {
		lemma_mul_comm(b, mod_(a, m));
		cong_mod_(sub_(mul_(b, mod_(a, m)), mul_(b, a)), m, sub_(mul_(mod_(a, m), b), mul_(b, a)), m);
		cong_sub_(mul_(b, mod_(a, m)), mul_(b, a), mul_(mod_(a, m), b), mul_(b, a));
		lemma_eq_ref(m);
		lemma_eq_ref(mul_(b, a));
	}
	let temp_73_0 = (sub_((mul_(d, a)), (mul_(d, b))));
	let temp_73_1 = (sub_((mul_(d, a)), (mul_(b, d))));
	assert(eq_(temp_73_0, temp_73_1)) by {
		cong_sub_(mul_(d, a), mul_(d, b), mul_(d, a), mul_(b, d));
		lemma_mul_comm(d, b);
		lemma_eq_ref(mul_(d, a));
	}
	let temp_74_0 = (mul_((mul_(c, b)), (mul_(a, a))));
	let temp_74_1 = (mul_(c, (mul_(b, (mul_(a, a))))));
	assert(eq_(temp_74_0, temp_74_1)) by {
		lemma_eq_sym(temp_74_1, temp_74_0);
		lemma_mul_assoc(c, b, mul_(a, a));
	}
	let temp_75_0 = (mod_((mul_((mul_(c, a)), d)), m));
	let temp_75_1 = (mod_((mul_(c, (mul_(a, d)))), m));
	assert(eq_(temp_75_0, temp_75_1)) by {
		lemma_mul_assoc(c, a, d);
		cong_mod_(mul_(mul_(c, a), d), m, mul_(c, mul_(a, d)), m);
		lemma_eq_sym(mul_(c, mul_(a, d)), mul_(mul_(c, a), d));
		lemma_eq_ref(m);
	}
	let temp_76_0 = (mul_((mul_(d, b)), (mod_((mul_(c, c)), m))));
	let temp_76_1 = (mul_((mod_((mul_(c, c)), m)), (mul_(d, b))));
	assert(eq_(temp_76_0, temp_76_1)) by {
		lemma_mul_comm(mul_(d, b), mod_(mul_(c, c), m));
	}
	let temp_77_0 = (mul_((mul_(a, a)), (mod_((mul_(d, a)), m))));
	let temp_77_1 = (mul_(a, (mul_(a, (mod_((mul_(d, a)), m))))));
	assert(eq_(temp_77_0, temp_77_1)) by {
		lemma_eq_sym(temp_77_1, temp_77_0);
		lemma_mul_assoc(a, a, mod_(mul_(d, a), m));
	}
	let temp_78_0 = (mul_((sub_(b, a)), (mul_(c, c))));
	let temp_78_1 = (mul_((sub_(b, a)), (mul_(c, c))));
	assert(eq_(temp_78_0, temp_78_1)) by {
		lemma_eq_ref(temp_78_0);
	}
	let temp_79_0 = (mul_((mul_(d, c)), (sub_(a, a))));
	let temp_79_1 = (mul_((sub_(a, a)), (mul_(d, c))));
	assert(eq_(temp_79_0, temp_79_1)) by {
		lemma_mul_comm(mul_(d, c), sub_(a, a));
	}
	let temp_80_0 = (mul_((mul_(a, d)), (mul_(c, c))));
	let temp_80_1 = (mul_(a, (mul_(d, (mul_(c, c))))));
	assert(eq_(temp_80_0, temp_80_1)) by {
		lemma_eq_sym(temp_80_1, temp_80_0);
		lemma_mul_assoc(a, d, mul_(c, c));
	}
	let temp_81_0 = (mul_((mul_(as_elem(89), c)), as_elem(3)));
	let temp_81_1 = (mul_((mul_(c, as_elem(89))), as_elem(3)));
	assert(eq_(temp_81_0, temp_81_1)) by {
		cong_mul_(mul_(as_elem(89), c), as_elem(3), mul_(c, as_elem(89)), as_elem(3));
		lemma_mul_comm(as_elem(89), c);
		lemma_eq_ref(as_elem(3));
	}
	let temp_82_0 = (sub_((mod_((mul_(c, b)), m)), (mul_(a, d))));
	let temp_82_1 = (sub_((mod_((add_((mul_((add_((mul_(d, c)), (mod_((mul_(b, c)), m)))), m)), (mul_(c, b)))), m)), (mul_(a, d))));
	assert(eq_(temp_82_0, temp_82_1)) by {
		lemma_mod_mul_vanish(mul_(c, b), add_(mul_(d, c), mod_(mul_(b, c), m)), m);
		cong_sub_(mod_(mul_(c, b), m), mul_(a, d), mod_(add_(mul_(add_(mul_(d, c), mod_(mul_(b, c), m)), m), mul_(c, b)), m), mul_(a, d));
		lemma_eq_ref(mul_(a, d));
	}
	let temp_83_0 = (add_((mul_(b, c)), (mul_(b, a))));
	let temp_83_1 = (add_((mul_(c, b)), (mul_(b, a))));
	assert(eq_(temp_83_0, temp_83_1)) by {
		cong_add_(mul_(b, c), mul_(b, a), mul_(c, b), mul_(b, a));
		lemma_mul_comm(b, c);
		lemma_eq_ref(mul_(b, a));
	}
	let temp_84_0 = (mul_((mul_(a, b)), (mul_(c, b))));
	let temp_84_1 = (mul_((mul_(c, b)), (mul_(a, b))));
	assert(eq_(temp_84_0, temp_84_1)) by {
		lemma_mul_comm(mul_(a, b), mul_(c, b));
	}
	let temp_85_0 = (mul_((mul_(a, a)), (mul_(d, (mod_(b, m))))));
	let temp_85_1 = (mul_(a, (mul_(a, (mul_(d, (mod_(b, m))))))));
	assert(eq_(temp_85_0, temp_85_1)) by {
		lemma_mul_assoc(a, a, mul_(d, mod_(b, m)));
		lemma_eq_sym(temp_85_1, temp_85_0);
	}
	let temp_86_0 = (mul_((mul_(d, d)), (mul_(d, c))));
	let temp_86_1 = (mul_((mul_(d, c)), (mul_(d, d))));
	assert(eq_(temp_86_0, temp_86_1)) by {
		lemma_mul_comm(mul_(d, d), mul_(d, c));
	}
	let temp_87_0 = (mul_((mul_(b, c)), (sub_(b, b))));
	let temp_87_1 = (mul_((sub_(b, b)), (mul_(b, c))));
	assert(eq_(temp_87_0, temp_87_1)) by {
		lemma_mul_comm(mul_(b, c), sub_(b, b));
	}
	let temp_88_0 = (sub_((mul_((mod_(c, m)), d)), (mul_((mod_(a, m)), (mod_(c, m))))));
	let temp_88_1 = (sub_((mul_((mod_(c, m)), d)), (mul_((mod_((add_((mul_((mul_((mul_(b, d)), (mul_(b, c)))), m)), a)), m)), (mod_(c, m))))));
	assert(eq_(temp_88_0, temp_88_1)) by {
		lemma_mod_mul_vanish(a, mul_(mul_(b, d), mul_(b, c)), m);
		cong_sub_(mul_(mod_(c, m), d), mul_(mod_(a, m), mod_(c, m)), mul_(mod_(c, m), d), mul_(mod_(add_(mul_(mul_(mul_(b, d), mul_(b, c)), m), a), m), mod_(c, m)));
		lemma_eq_ref(mul_(mod_(c, m), d));
		cong_mul_(mod_(a, m), mod_(c, m), mod_(add_(mul_(mul_(mul_(b, d), mul_(b, c)), m), a), m), mod_(c, m));
		lemma_eq_ref(mod_(c, m));
	}
	let temp_89_0 = (mul_((mul_(a, as_elem(57))), (mul_(d, d))));
	let temp_89_1 = (mul_((mul_(d, d)), (mul_(a, as_elem(57)))));
	assert(eq_(temp_89_0, temp_89_1)) by {
		lemma_mul_comm(mul_(a, as_elem(57)), mul_(d, d));
	}
	let temp_90_0 = (mod_((mul_((mod_((add_(d, d)), m)), (mul_(c, d)))), m));
	let temp_90_1 = (mod_((mul_((mod_((add_(d, d)), m)), (mul_(d, c)))), m));
	assert(eq_(temp_90_0, temp_90_1)) by {
		lemma_mul_comm(c, d);
		cong_mod_(mul_(mod_(add_(d, d), m), mul_(c, d)), m, mul_(mod_(add_(d, d), m), mul_(d, c)), m);
		lemma_eq_ref(mod_(add_(d, d), m));
		cong_mul_(mod_(add_(d, d), m), mul_(c, d), mod_(add_(d, d), m), mul_(d, c));
		lemma_eq_ref(m);
	}
	let temp_91_0 = (mul_((mul_(b, b)), (mul_(c, b))));
	let temp_91_1 = (mul_(b, (mul_(b, (mul_(c, b))))));
	assert(eq_(temp_91_0, temp_91_1)) by {
		lemma_eq_sym(temp_91_1, temp_91_0);
		lemma_mul_assoc(b, b, mul_(c, b));
	}
	let temp_92_0 = (sub_((mul_(b, d)), (mod_((mul_((mod_(a, m)), d)), m))));
	let temp_92_1 = (sub_((mul_(b, d)), (mod_((mul_((mod_((sub_(a, (mul_((add_((mul_(b, c)), (mul_((mod_(d, m)), c)))), m)))), m)), d)), m))));
	assert(eq_(temp_92_0, temp_92_1)) by {
		lemma_mod_mul_vanish(a, add_(mul_(b, c), mul_(mod_(d, m), c)), m);
		cong_sub_(mul_(b, d), mod_(mul_(mod_(a, m), d), m), mul_(b, d), mod_(mul_(mod_(sub_(a, mul_(add_(mul_(b, c), mul_(mod_(d, m), c)), m)), m), d), m));
		cong_mod_(mul_(mod_(sub_(a, mul_(add_(mul_(b, c), mul_(mod_(d, m), c)), m)), m), d), m, mul_(mod_(a, m), d), m);
		lemma_eq_sym(mod_(mul_(mod_(sub_(a, mul_(add_(mul_(b, c), mul_(mod_(d, m), c)), m)), m), d), m), mod_(mul_(mod_(a, m), d), m));
		lemma_eq_ref(mul_(b, d));
		lemma_eq_sym(mod_(a, m), mod_(sub_(a, mul_(add_(mul_(b, c), mul_(mod_(d, m), c)), m)), m));
		lemma_eq_ref(d);
		cong_mul_(mod_(sub_(a, mul_(add_(mul_(b, c), mul_(mod_(d, m), c)), m)), m), d, mod_(a, m), d);
		lemma_eq_ref(m);
	}
	let temp_93_0 = (sub_((mod_((mul_(b, a)), m)), (mod_((mul_(b, a)), m))));
	let temp_93_1 = (sub_((mod_((mul_(b, a)), m)), (mod_((mul_(a, b)), m))));
	assert(eq_(temp_93_0, temp_93_1)) by {
		cong_sub_(mod_(mul_(b, a), m), mod_(mul_(b, a), m), mod_(mul_(b, a), m), mod_(mul_(a, b), m));
		lemma_mul_comm(b, a);
		cong_mod_(mul_(b, a), m, mul_(a, b), m);
		lemma_eq_ref(m);
		lemma_eq_ref(mod_(mul_(b, a), m));
	}
	let temp_94_0 = (mul_((mul_(c, d)), (mod_((sub_(as_elem(75), a)), m))));
	let temp_94_1 = (mul_(c, (mul_(d, (mod_((sub_(as_elem(75), a)), m))))));
	assert(eq_(temp_94_0, temp_94_1)) by {
		lemma_mul_assoc(c, d, mod_(sub_(as_elem(75), a), m));
		lemma_eq_sym(temp_94_1, temp_94_0);
	}
	let temp_95_0 = (mul_((add_(a, c)), (mul_(b, a))));
	let temp_95_1 = (mul_((add_(a, c)), (mul_(a, b))));
	assert(eq_(temp_95_0, temp_95_1)) by {
		cong_mul_(add_(a, c), mul_(b, a), add_(a, c), mul_(a, b));
		lemma_mul_comm(b, a);
		lemma_eq_ref(add_(a, c));
	}
	let temp_96_0 = (mul_((mul_(b, b)), (mul_(a, b))));
	let temp_96_1 = (mul_((mul_((mul_(b, b)), a)), b));
	assert(eq_(temp_96_0, temp_96_1)) by {
		lemma_mul_assoc(mul_(b, b), a, b);
	}
	let temp_97_0 = (mul_((add_(a, b)), (mod_((sub_(b, c)), m))));
	let temp_97_1 = (add_((mul_(a, (mod_((sub_(b, c)), m)))), (mul_(b, (mod_((sub_(b, c)), m))))));
	assert(eq_(temp_97_0, temp_97_1)) by {
		lemma_mul_dist(a, b, mod_(sub_(b, c), m));
	}
	let temp_98_0 = (mul_((sub_(c, c)), (mul_(c, a))));
	let temp_98_1 = (mul_((mul_((sub_(c, c)), c)), a));
	assert(eq_(temp_98_0, temp_98_1)) by {
		lemma_mul_assoc(sub_(c, c), c, a);
	}
	let temp_99_0 = (sub_((mul_(d, b)), (sub_(a, d))));
	let temp_99_1 = (sub_((mul_(b, d)), (sub_(a, d))));
	assert(eq_(temp_99_0, temp_99_1)) by {
		cong_sub_(mul_(d, b), sub_(a, d), mul_(b, d), sub_(a, d));
		lemma_mul_comm(d, b);
		lemma_eq_ref(sub_(a, d));
	}
	let temp_100_0 = (mul_((mul_(c, b)), (mul_(b, b))));
	let temp_100_1 = (mul_((mul_(b, c)), (mul_(b, b))));
	assert(eq_(temp_100_0, temp_100_1)) by {
		cong_mul_(mul_(c, b), mul_(b, b), mul_(b, c), mul_(b, b));
		lemma_mul_comm(c, b);
		lemma_mul_comm(b, b);
	}
	let temp_101_0 = (mul_((mul_((mod_(c, m)), (mod_(c, m)))), (mul_(c, b))));
	let temp_101_1 = (mul_((mod_(c, m)), (mul_((mod_(c, m)), (mul_(c, b))))));
	assert(eq_(temp_101_0, temp_101_1)) by {
		lemma_eq_sym(temp_101_1, temp_101_0);
		lemma_mul_assoc(mod_(c, m), mod_(c, m), mul_(c, b));
	}
	let temp_102_0 = (sub_((mul_(d, b)), (mod_((mul_(c, c)), m))));
	let temp_102_1 = (sub_((mul_(b, d)), (mod_((mul_(c, c)), m))));
	assert(eq_(temp_102_0, temp_102_1)) by {
		lemma_mul_comm(d, b);
		cong_sub_(mul_(d, b), mod_(mul_(c, c), m), mul_(b, d), mod_(mul_(c, c), m));
		lemma_eq_ref(mod_(mul_(c, c), m));
	}
	let temp_103_0 = (mod_((mul_((mod_((mul_(b, b)), m)), (mul_(d, b)))), m));
	let temp_103_1 = (mod_((mul_((mod_((add_((mul_((mul_((sub_(b, a)), (mul_(a, a)))), m)), (mul_(b, b)))), m)), (mul_(d, b)))), m));
	assert(eq_(temp_103_0, temp_103_1)) by {
		lemma_mod_mul_vanish(mul_(b, b), mul_(sub_(b, a), mul_(a, a)), m);
		cong_mod_(mul_(mod_(mul_(b, b), m), mul_(d, b)), m, mul_(mod_(add_(mul_(mul_(sub_(b, a), mul_(a, a)), m), mul_(b, b)), m), mul_(d, b)), m);
		lemma_eq_ref(m);
		cong_mul_(mod_(mul_(b, b), m), mul_(d, b), mod_(add_(mul_(mul_(sub_(b, a), mul_(a, a)), m), mul_(b, b)), m), mul_(d, b));
		lemma_eq_ref(mul_(d, b));
	}
	let temp_104_0 = (mod_((mul_(c, (mul_(b, (mod_(b, m)))))), m));
	let temp_104_1 = (mod_((mul_((mul_(b, (mod_(b, m)))), c)), m));
	assert(eq_(temp_104_0, temp_104_1)) by {
		cong_mod_(mul_(c, mul_(b, mod_(b, m))), m, mul_(mul_(b, mod_(b, m)), c), m);
		lemma_mul_comm(c, mul_(b, mod_(b, m)));
		lemma_eq_ref(m);
	}
	let temp_105_0 = (mul_((mod_((add_(a, b)), m)), (mul_(as_elem(55), a))));
	let temp_105_1 = (mul_((mul_((mod_((add_(a, b)), m)), as_elem(55))), a));
	assert(eq_(temp_105_0, temp_105_1)) by {
		lemma_mul_assoc(mod_(add_(a, b), m), as_elem(55), a);
	}
	let temp_106_0 = (mul_((sub_(c, b)), (add_(d, d))));
	let temp_106_1 = (add_((mul_((sub_(c, b)), d)), (mul_((sub_(c, b)), d))));
	assert(eq_(temp_106_0, temp_106_1)) by {
		lemma_mul_dist(sub_(c, b), d, d);
	}
	let temp_107_0 = (mul_(c, (sub_((mod_(b, m)), c))));
	let temp_107_1 = (mul_(c, (sub_((mod_((add_((mul_((mul_((mul_(c, b)), (add_(c, (mod_(d, m)))))), m)), b)), m)), c))));
	assert(eq_(temp_107_0, temp_107_1)) by {
		lemma_mod_mul_vanish(b, mul_(mul_(c, b), add_(c, mod_(d, m))), m);
		cong_mul_(c, sub_(mod_(b, m), c), c, sub_(mod_(add_(mul_(mul_(mul_(c, b), add_(c, mod_(d, m))), m), b), m), c));
		lemma_eq_ref(c);
		cong_sub_(mod_(b, m), c, mod_(add_(mul_(mul_(mul_(c, b), add_(c, mod_(d, m))), m), b), m), c);
	}

}

} // verus!