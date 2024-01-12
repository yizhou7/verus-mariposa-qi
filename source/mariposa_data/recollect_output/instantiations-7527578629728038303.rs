use builtin_macros::*;
// use builtin::*;
mod nl_basics;
use crate::nl_basics::*;
verus! {

pub proof fn free_0(a: Elem, b: Elem, c: Elem, d: Elem, m: Elem)
{
	let temp_0_0 = (mul_((mul_(a, b)), (mul_(b, a))));
	let temp_0_1 = (mul_((mul_(b, a)), (mul_(b, a))));
	assert(eq_(temp_0_0, temp_0_1)) by {
		cong_mul_(mul_(a, b), mul_(b, a), mul_(b, a), mul_(b, a));
		lemma_mul_comm(a, b);
		lemma_eq_ref(mul_(b, a));
	}
	let temp_1_0 = (mul_((mul_(d, c)), (mul_(b, (mod_(d, m))))));
	let temp_1_1 = (mul_((mul_(d, c)), (mul_(b, (mod_((add_(d, (mul_((mul_((mod_((mul_(b, d)), m)), (add_(b, b)))), m)))), m))))));
	assert(eq_(temp_1_0, temp_1_1)) by {
		lemma_eq_ref(mul_(d, c));
		lemma_mod_mul_vanish(d, mul_(mod_(mul_(b, d), m), add_(b, b)), m);
		cong_mul_(mul_(d, c), mul_(b, mod_(d, m)), mul_(d, c), mul_(b, mod_(add_(d, mul_(mul_(mod_(mul_(b, d), m), add_(b, b)), m)), m)));
		cong_mul_(b, mod_(d, m), b, mod_(add_(d, mul_(mul_(mod_(mul_(b, d), m), add_(b, b)), m)), m));
		lemma_eq_ref(b);
	}
	let temp_2_0 = (mul_((mul_(b, a)), (mul_(d, d))));
	let temp_2_1 = (mul_((mul_((mul_(b, a)), d)), d));
	assert(eq_(temp_2_0, temp_2_1)) by {
		lemma_mul_assoc(mul_(b, a), d, d);
	}
	let temp_3_0 = (mul_((mul_(d, a)), (mul_(b, b))));
	let temp_3_1 = (mul_((mul_(b, b)), (mul_(d, a))));
	assert(eq_(temp_3_0, temp_3_1)) by {
		lemma_mul_comm(mul_(d, a), mul_(b, b));
	}
	let temp_4_0 = (mul_((mul_(c, (mod_(d, m)))), (add_(b, a))));
	let temp_4_1 = (add_((mul_((mul_(c, (mod_(d, m)))), b)), (mul_((mul_(c, (mod_(d, m)))), a))));
	assert(eq_(temp_4_0, temp_4_1)) by {
		lemma_mul_dist(mul_(c, mod_(d, m)), b, a);
	}
	let temp_5_0 = (mul_((mul_(d, a)), (mod_((mul_(a, b)), m))));
	let temp_5_1 = (mul_(d, (mul_(a, (mod_((mul_(a, b)), m))))));
	assert(eq_(temp_5_0, temp_5_1)) by {
		lemma_mul_assoc(d, a, mod_(mul_(a, b), m));
		lemma_eq_sym(temp_5_1, temp_5_0);
	}
	let temp_6_0 = (mul_((add_(b, d)), (mul_(d, d))));
	let temp_6_1 = (mul_((add_(b, d)), (mul_(d, d))));
	assert(eq_(temp_6_0, temp_6_1)) by {
		lemma_eq_ref(temp_6_0);
	}
	let temp_7_0 = (mul_((mul_(d, a)), (sub_(d, c))));
	let temp_7_1 = (mul_(d, (mul_(a, (sub_(d, c))))));
	assert(eq_(temp_7_0, temp_7_1)) by {
		lemma_eq_sym(temp_7_1, temp_7_0);
		lemma_mul_assoc(d, a, sub_(d, c));
	}
	let temp_8_0 = (add_((mul_(b, d)), (add_(c, c))));
	let temp_8_1 = (add_((mul_(d, b)), (add_(c, c))));
	assert(eq_(temp_8_0, temp_8_1)) by {
		cong_add_(mul_(b, d), add_(c, c), mul_(d, b), add_(c, c));
		lemma_add_comm(c, c);
		lemma_mul_comm(b, d);
	}
	let temp_9_0 = (mod_((mul_((mul_(a, b)), (mul_(b, (mod_(c, m)))))), m));
	let temp_9_1 = (mod_((mul_(a, (mul_(b, (mul_(b, (mod_(c, m)))))))), m));
	assert(eq_(temp_9_0, temp_9_1)) by {
		lemma_mul_assoc(a, b, mul_(b, mod_(c, m)));
		cong_mod_(mul_(mul_(a, b), mul_(b, mod_(c, m))), m, mul_(a, mul_(b, mul_(b, mod_(c, m)))), m);
		lemma_eq_ref(m);
		lemma_eq_sym(mul_(a, mul_(b, mul_(b, mod_(c, m)))), mul_(mul_(a, b), mul_(b, mod_(c, m))));
	}
	let temp_10_0 = (sub_((mul_(b, d)), (mul_(c, c))));
	let temp_10_1 = (sub_((mul_(b, d)), (mul_(c, c))));
	assert(eq_(temp_10_0, temp_10_1)) by {
		lemma_eq_ref(temp_10_0);
	}
	let temp_11_0 = (mul_((mul_(a, d)), (mul_(a, c))));
	let temp_11_1 = (mul_((mul_(a, c)), (mul_(a, d))));
	assert(eq_(temp_11_0, temp_11_1)) by {
		lemma_mul_comm(mul_(a, d), mul_(a, c));
	}
	let temp_12_0 = (mod_((mul_(a, (mod_((mul_((mod_(b, m)), c)), m)))), m));
	let temp_12_1 = (mod_((mod_((mul_(a, (mul_((mod_(b, m)), c)))), m)), m));
	assert(eq_(temp_12_0, temp_12_1)) by {
		lemma_mod_mul_noop(a, mul_(mod_(b, m), c), m);
		lemma_eq_sym(temp_12_1, temp_12_0);
	}
	let temp_13_0 = (add_((mul_(d, (mod_(as_elem(11), m)))), (mul_(c, d))));
	let temp_13_1 = (add_((mul_(d, (mod_((sub_(as_elem(11), (mul_((mul_((sub_(a, d)), (mul_(d, a)))), m)))), m)))), (mul_(c, d))));
	assert(eq_(temp_13_0, temp_13_1)) by {
		lemma_mod_mul_vanish(as_elem(11), mul_(sub_(a, d), mul_(d, a)), m);
		cong_add_(mul_(d, mod_(as_elem(11), m)), mul_(c, d), mul_(d, mod_(sub_(as_elem(11), mul_(mul_(sub_(a, d), mul_(d, a)), m)), m)), mul_(c, d));
		lemma_eq_ref(d);
		cong_mul_(d, mod_(as_elem(11), m), d, mod_(sub_(as_elem(11), mul_(mul_(sub_(a, d), mul_(d, a)), m)), m));
		lemma_eq_ref(mul_(c, d));
	}
	let temp_14_0 = (add_((mul_(b, c)), (mul_(b, c))));
	let temp_14_1 = (mul_(b, (add_(c, c))));
	assert(eq_(temp_14_0, temp_14_1)) by {
		lemma_eq_sym(temp_14_1, temp_14_0);
		lemma_mul_dist(b, c, c);
	}
	let temp_15_0 = (add_((mul_(c, b)), (mul_(b, c))));
	let temp_15_1 = (add_((mul_(b, c)), (mul_(b, c))));
	assert(eq_(temp_15_0, temp_15_1)) by {
		cong_add_(mul_(c, b), mul_(b, c), mul_(b, c), mul_(b, c));
		lemma_mul_comm(c, b);
		lemma_eq_ref(mul_(b, c));
	}
	let temp_16_0 = (mul_((add_(c, b)), (mul_((mod_(d, m)), (mod_(d, m))))));
	let temp_16_1 = (mul_((mul_((mod_(d, m)), (mod_(d, m)))), (add_(c, b))));
	assert(eq_(temp_16_0, temp_16_1)) by {
		lemma_mul_comm(add_(c, b), mul_(mod_(d, m), mod_(d, m)));
	}
	let temp_17_0 = (mul_((mul_((mod_(c, m)), c)), (mul_(b, c))));
	let temp_17_1 = (mul_((mul_((mod_(c, m)), c)), (mul_(c, b))));
	assert(eq_(temp_17_0, temp_17_1)) by {
		cong_mul_(mul_(mod_(c, m), c), mul_(b, c), mul_(mod_(c, m), c), mul_(c, b));
		lemma_mul_comm(b, c);
		lemma_eq_ref(mul_(mod_(c, m), c));
	}
	let temp_18_0 = (mul_((mul_(a, b)), (mul_(c, c))));
	let temp_18_1 = (mul_((mul_(a, b)), (mul_(c, c))));
	assert(eq_(temp_18_0, temp_18_1)) by {
		lemma_eq_ref(temp_18_0);
	}
	let temp_19_0 = (mul_((mul_(c, d)), (mul_(a, (mod_(d, m))))));
	let temp_19_1 = (mul_((mul_(c, d)), (mul_(a, (mod_((sub_(d, (mul_((mul_((mul_(a, d)), (mul_(b, b)))), m)))), m))))));
	assert(eq_(temp_19_0, temp_19_1)) by {
		lemma_mod_mul_vanish(d, mul_(mul_(a, d), mul_(b, b)), m);
		cong_mul_(mul_(c, d), mul_(a, mod_(d, m)), mul_(c, d), mul_(a, mod_(sub_(d, mul_(mul_(mul_(a, d), mul_(b, b)), m)), m)));
		lemma_eq_ref(a);
		lemma_eq_ref(mul_(c, d));
		cong_mul_(a, mod_(d, m), a, mod_(sub_(d, mul_(mul_(mul_(a, d), mul_(b, b)), m)), m));
	}
	let temp_20_0 = (mul_((mod_((add_(b, c)), m)), (mul_(d, b))));
	let temp_20_1 = (mul_((mod_((add_((mul_((mul_((mod_((mul_(b, d)), m)), (mul_(c, a)))), m)), (add_(b, c)))), m)), (mul_(d, b))));
	assert(eq_(temp_20_0, temp_20_1)) by {
		lemma_mod_mul_vanish(add_(b, c), mul_(mod_(mul_(b, d), m), mul_(c, a)), m);
		cong_mul_(mod_(add_(b, c), m), mul_(d, b), mod_(add_(mul_(mul_(mod_(mul_(b, d), m), mul_(c, a)), m), add_(b, c)), m), mul_(d, b));
		lemma_eq_ref(mul_(d, b));
	}
	let temp_21_0 = (mul_((mul_((mod_(b, m)), (mod_(a, m)))), (mul_(c, (mod_(as_elem(16), m))))));
	let temp_21_1 = (mul_((mod_(b, m)), (mul_((mod_(a, m)), (mul_(c, (mod_(as_elem(16), m))))))));
	assert(eq_(temp_21_0, temp_21_1)) by {
		lemma_mul_assoc(mod_(b, m), mod_(a, m), mul_(c, mod_(as_elem(16), m)));
		lemma_eq_sym(temp_21_1, temp_21_0);
	}
	let temp_22_0 = (mod_((mul_((mul_(a, c)), (mul_(a, a)))), m));
	let temp_22_1 = (mod_((mul_(a, (mul_(c, (mul_(a, a)))))), m));
	assert(eq_(temp_22_0, temp_22_1)) by {
		lemma_mul_assoc(a, c, mul_(a, a));
		cong_mod_(mul_(mul_(a, c), mul_(a, a)), m, mul_(a, mul_(c, mul_(a, a))), m);
		lemma_eq_sym(mul_(a, mul_(c, mul_(a, a))), mul_(mul_(a, c), mul_(a, a)));
		lemma_eq_ref(m);
	}
	let temp_23_0 = (mul_(a, (mul_(c, c))));
	let temp_23_1 = (mul_(a, (mul_(c, c))));
	assert(eq_(temp_23_0, temp_23_1)) by {
		lemma_eq_ref(temp_23_0);
	}
	let temp_24_0 = (mul_((mul_(c, a)), (mul_(b, b))));
	let temp_24_1 = (mul_((mul_((mul_(c, a)), b)), b));
	assert(eq_(temp_24_0, temp_24_1)) by {
		lemma_mul_assoc(mul_(c, a), b, b);
	}
	let temp_25_0 = (mod_((mul_((mul_(as_elem(59), b)), (mul_(b, c)))), m));
	let temp_25_1 = (mod_((add_((mul_((mul_((mul_(c, b)), (mul_(a, b)))), m)), (mul_((mul_(as_elem(59), b)), (mul_(b, c)))))), m));
	assert(eq_(temp_25_0, temp_25_1)) by {
		lemma_mod_mul_vanish(mul_(mul_(as_elem(59), b), mul_(b, c)), mul_(mul_(c, b), mul_(a, b)), m);
	}
	let temp_26_0 = (mod_((sub_((add_((mod_(a, m)), d)), (mul_(c, b)))), m));
	let temp_26_1 = (mod_((sub_((add_((mod_(a, m)), d)), (mul_(b, c)))), m));
	assert(eq_(temp_26_0, temp_26_1)) by {
		lemma_mul_comm(c, b);
		cong_mod_(sub_(add_(mod_(a, m), d), mul_(c, b)), m, sub_(add_(mod_(a, m), d), mul_(b, c)), m);
		cong_sub_(add_(mod_(a, m), d), mul_(c, b), add_(mod_(a, m), d), mul_(b, c));
		lemma_eq_ref(m);
		lemma_eq_ref(add_(mod_(a, m), d));
	}
	let temp_27_0 = (mul_((mul_(b, b)), (mul_(c, b))));
	let temp_27_1 = (mul_((mul_(c, b)), (mul_(b, b))));
	assert(eq_(temp_27_0, temp_27_1)) by {
		lemma_mul_comm(mul_(b, b), mul_(c, b));
	}
	let temp_28_0 = (mod_((mul_((mul_(c, d)), (mul_(a, (mod_(c, m)))))), m));
	let temp_28_1 = (mod_((mul_((mul_(c, d)), (mul_((mod_(c, m)), a)))), m));
	assert(eq_(temp_28_0, temp_28_1)) by {
		lemma_mul_comm(a, mod_(c, m));
		cong_mod_(mul_(mul_(c, d), mul_(a, mod_(c, m))), m, mul_(mul_(c, d), mul_(mod_(c, m), a)), m);
		lemma_eq_ref(mul_(c, d));
		cong_mul_(mul_(c, d), mul_(a, mod_(c, m)), mul_(c, d), mul_(mod_(c, m), a));
		lemma_eq_ref(m);
	}
	let temp_29_0 = (sub_((mul_(c, a)), (mul_(a, d))));
	let temp_29_1 = (sub_((mul_(a, c)), (mul_(a, d))));
	assert(eq_(temp_29_0, temp_29_1)) by {
		cong_sub_(mul_(c, a), mul_(a, d), mul_(a, c), mul_(a, d));
		lemma_mul_comm(c, a);
		lemma_eq_ref(mul_(a, d));
	}
	let temp_30_0 = (mul_((add_(d, a)), (mul_(a, d))));
	let temp_30_1 = (mul_((mul_((add_(d, a)), a)), d));
	assert(eq_(temp_30_0, temp_30_1)) by {
		lemma_mul_assoc(add_(d, a), a, d);
	}
	let temp_31_0 = (sub_((mul_(as_elem(66), d)), (mul_(c, d))));
	let temp_31_1 = (sub_((mul_(d, as_elem(66))), (mul_(c, d))));
	assert(eq_(temp_31_0, temp_31_1)) by {
		cong_sub_(mul_(as_elem(66), d), mul_(c, d), mul_(d, as_elem(66)), mul_(c, d));
		lemma_mul_comm(as_elem(66), d);
		lemma_eq_ref(mul_(c, d));
	}
	let temp_32_0 = (sub_((mod_((mul_(c, (mod_(d, m)))), m)), (mul_(b, d))));
	let temp_32_1 = (sub_((mod_((mod_((mul_(d, c)), m)), m)), (mul_(b, d))));
	assert(eq_(temp_32_0, temp_32_1)) by {
		lemma_mod_mul_noop(d, c, m);
		cong_sub_(mod_(mul_(c, mod_(d, m)), m), mul_(b, d), mod_(mod_(mul_(d, c), m), m), mul_(b, d));
		lemma_eq_sym(mod_(mod_(mul_(d, c), m), m), mod_(mul_(c, mod_(d, m)), m));
		lemma_eq_ref(mul_(b, d));
	}
	let temp_33_0 = (mul_((mul_(c, c)), (mod_((sub_(a, d)), m))));
	let temp_33_1 = (mul_((mul_(c, c)), (mod_((add_((mul_((mul_((mul_(b, d)), (sub_(d, d)))), m)), (sub_(a, d)))), m))));
	assert(eq_(temp_33_0, temp_33_1)) by {
		lemma_mul_comm(c, c);
		lemma_mod_mul_vanish(sub_(a, d), mul_(mul_(b, d), sub_(d, d)), m);
		cong_mul_(mul_(c, c), mod_(sub_(a, d), m), mul_(c, c), mod_(add_(mul_(mul_(mul_(b, d), sub_(d, d)), m), sub_(a, d)), m));
	}
	let temp_34_0 = (mul_((sub_(b, d)), (mul_((mod_(a, m)), b))));
	let temp_34_1 = (mul_((mul_((sub_(b, d)), (mod_(a, m)))), b));
	assert(eq_(temp_34_0, temp_34_1)) by {
		lemma_mul_assoc(sub_(b, d), mod_(a, m), b);
	}
	let temp_35_0 = (mul_((mul_(a, b)), (mul_(a, c))));
	let temp_35_1 = (mul_(a, (mul_(b, (mul_(a, c))))));
	assert(eq_(temp_35_0, temp_35_1)) by {
		lemma_eq_sym(temp_35_1, temp_35_0);
		lemma_mul_assoc(a, b, mul_(a, c));
	}
	let temp_36_0 = (mul_((mul_(d, d)), (sub_(a, d))));
	let temp_36_1 = (mul_((mul_(d, d)), (sub_(a, d))));
	assert(eq_(temp_36_0, temp_36_1)) by {
		lemma_eq_ref(temp_36_0);
	}
	let temp_37_0 = (mul_((mul_(b, b)), (mul_(a, c))));
	let temp_37_1 = (mul_(b, (mul_(b, (mul_(a, c))))));
	assert(eq_(temp_37_0, temp_37_1)) by {
		lemma_eq_sym(temp_37_1, temp_37_0);
		lemma_mul_assoc(b, b, mul_(a, c));
	}
	let temp_38_0 = (mul_((mod_((mul_((mod_(c, m)), d)), m)), (mul_(c, b))));
	let temp_38_1 = (mul_((mod_((mul_(d, (mod_(c, m)))), m)), (mul_(c, b))));
	assert(eq_(temp_38_0, temp_38_1)) by {
		cong_mod_(mul_(mod_(c, m), d), m, mul_(d, mod_(c, m)), m);
		lemma_eq_ref(mul_(c, b));
		lemma_mul_comm(mod_(c, m), d);
		cong_mul_(mod_(mul_(mod_(c, m), d), m), mul_(c, b), mod_(mul_(d, mod_(c, m)), m), mul_(c, b));
		lemma_eq_ref(m);
	}
	let temp_39_0 = (mul_((mul_(a, (mod_(b, m)))), (mul_(a, (mod_(d, m))))));
	let temp_39_1 = (mul_((mul_(a, (mod_(b, m)))), (mul_(a, (mod_((sub_(d, (mul_((mul_((mul_(d, d)), (mul_(d, a)))), m)))), m))))));
	assert(eq_(temp_39_0, temp_39_1)) by {
		lemma_eq_ref(mul_(a, mod_(b, m)));
		cong_mul_(a, mod_(d, m), a, mod_(sub_(d, mul_(mul_(mul_(d, d), mul_(d, a)), m)), m));
		lemma_eq_ref(a);
		lemma_mod_mul_vanish(d, mul_(mul_(d, d), mul_(d, a)), m);
		cong_mul_(mul_(a, mod_(b, m)), mul_(a, mod_(d, m)), mul_(a, mod_(b, m)), mul_(a, mod_(sub_(d, mul_(mul_(mul_(d, d), mul_(d, a)), m)), m)));
	}
	let temp_40_0 = (mul_((mod_((mul_(b, as_elem(43))), m)), (mod_((mul_(c, d)), m))));
	let temp_40_1 = (mul_((mod_((mul_(b, as_elem(43))), m)), (mod_((mul_(d, c)), m))));
	assert(eq_(temp_40_0, temp_40_1)) by {
		lemma_mul_comm(c, d);
		cong_mul_(mod_(mul_(b, as_elem(43)), m), mod_(mul_(c, d), m), mod_(mul_(b, as_elem(43)), m), mod_(mul_(d, c), m));
		lemma_eq_ref(mod_(mul_(b, as_elem(43)), m));
		cong_mod_(mul_(c, d), m, mul_(d, c), m);
		lemma_eq_ref(m);
	}
	let temp_41_0 = (mul_((mul_(d, a)), (add_(d, d))));
	let temp_41_1 = (mul_((mul_(d, a)), (add_(d, d))));
	assert(eq_(temp_41_0, temp_41_1)) by {
		lemma_eq_ref(temp_41_0);
	}
	let temp_42_0 = (mul_((mul_(a, a)), (mul_((mod_(c, m)), b))));
	let temp_42_1 = (mul_((mul_(a, a)), (mul_((mod_((add_(c, (mul_((mod_((mul_((mul_(b, d)), (add_(a, (mod_(d, m)))))), m)), m)))), m)), b))));
	assert(eq_(temp_42_0, temp_42_1)) by {
		lemma_mul_comm(a, a);
		lemma_mod_mul_vanish(c, mod_(mul_(mul_(b, d), add_(a, mod_(d, m))), m), m);
		cong_mul_(mul_(a, a), mul_(mod_(c, m), b), mul_(a, a), mul_(mod_(add_(c, mul_(mod_(mul_(mul_(b, d), add_(a, mod_(d, m))), m), m)), m), b));
		lemma_eq_ref(b);
		cong_mul_(mod_(c, m), b, mod_(add_(c, mul_(mod_(mul_(mul_(b, d), add_(a, mod_(d, m))), m), m)), m), b);
	}
	let temp_43_0 = (mul_((add_(b, c)), (mul_(b, d))));
	let temp_43_1 = (mul_((add_(c, b)), (mul_(b, d))));
	assert(eq_(temp_43_0, temp_43_1)) by {
		cong_mul_(add_(b, c), mul_(b, d), add_(c, b), mul_(b, d));
		lemma_add_comm(b, c);
		lemma_eq_ref(mul_(b, d));
	}
	let temp_44_0 = (mul_((mul_(c, a)), (mul_(b, d))));
	let temp_44_1 = (mul_((mul_(b, d)), (mul_(c, a))));
	assert(eq_(temp_44_0, temp_44_1)) by {
		lemma_mul_comm(mul_(c, a), mul_(b, d));
	}
	let temp_45_0 = (sub_((mul_(c, a)), (mul_(b, d))));
	let temp_45_1 = (sub_((mul_(c, a)), (mul_(d, b))));
	assert(eq_(temp_45_0, temp_45_1)) by {
		cong_sub_(mul_(c, a), mul_(b, d), mul_(c, a), mul_(d, b));
		lemma_mul_comm(b, d);
		lemma_eq_ref(mul_(c, a));
	}
	let temp_46_0 = (add_((mul_(b, b)), (mul_(d, b))));
	let temp_46_1 = (mul_((add_(b, d)), b));
	assert(eq_(temp_46_0, temp_46_1)) by {
		lemma_eq_sym(temp_46_1, temp_46_0);
		lemma_mul_dist(b, d, b);
	}
	let temp_47_0 = (add_((mul_(b, b)), (mul_(a, a))));
	let temp_47_1 = (add_((mul_(a, a)), (mul_(b, b))));
	assert(eq_(temp_47_0, temp_47_1)) by {
		lemma_add_comm(mul_(b, b), mul_(a, a));
	}
	let temp_48_0 = (sub_((mod_((mul_(d, c)), m)), (mul_(d, c))));
	let temp_48_1 = (sub_((mod_((add_((mul_((mul_((mul_((mod_(a, m)), c)), (add_(a, c)))), m)), (mul_(d, c)))), m)), (mul_(d, c))));
	assert(eq_(temp_48_0, temp_48_1)) by {
		lemma_mod_mul_vanish(mul_(d, c), mul_(mul_(mod_(a, m), c), add_(a, c)), m);
		cong_sub_(mod_(mul_(d, c), m), mul_(d, c), mod_(add_(mul_(mul_(mul_(mod_(a, m), c), add_(a, c)), m), mul_(d, c)), m), mul_(d, c));
		lemma_eq_ref(mul_(d, c));
	}
	let temp_49_0 = (mul_((add_((mod_(c, m)), (mod_(c, m)))), (add_(c, b))));
	let temp_49_1 = (mul_((add_(c, b)), (add_((mod_(c, m)), (mod_(c, m))))));
	assert(eq_(temp_49_0, temp_49_1)) by {
		lemma_mul_comm(add_(mod_(c, m), mod_(c, m)), add_(c, b));
	}
	let temp_50_0 = (mul_((mul_(b, b)), (mul_(a, a))));
	let temp_50_1 = (mul_((mul_(a, a)), (mul_(b, b))));
	assert(eq_(temp_50_0, temp_50_1)) by {
		lemma_mul_comm(mul_(b, b), mul_(a, a));
	}
	let temp_51_0 = (add_((mul_(c, c)), d));
	let temp_51_1 = (add_(d, (mul_(c, c))));
	assert(eq_(temp_51_0, temp_51_1)) by {
		lemma_add_comm(mul_(c, c), d);
	}
	let temp_52_0 = (mul_((mul_(b, c)), (mod_((mul_(b, c)), m))));
	let temp_52_1 = (mul_((mul_(b, c)), (mod_((add_((mul_((mul_((mul_(d, b)), (mod_((mul_(c, d)), m)))), m)), (mul_(b, c)))), m))));
	assert(eq_(temp_52_0, temp_52_1)) by {
		lemma_mod_mul_vanish(mul_(b, c), mul_(mul_(d, b), mod_(mul_(c, d), m)), m);
		cong_mul_(mul_(b, c), mod_(mul_(b, c), m), mul_(b, c), mod_(add_(mul_(mul_(mul_(d, b), mod_(mul_(c, d), m)), m), mul_(b, c)), m));
		lemma_eq_ref(mul_(b, c));
	}
	let temp_53_0 = (mul_((mul_(c, b)), (mul_((mod_(d, m)), b))));
	let temp_53_1 = (mul_((mul_(c, b)), (mul_((mod_((sub_(d, (mul_((mul_(a, (mul_(d, a)))), m)))), m)), b))));
	assert(eq_(temp_53_0, temp_53_1)) by {
		lemma_mod_mul_vanish(d, mul_(a, mul_(d, a)), m);
		cong_mul_(mul_(c, b), mul_(mod_(d, m), b), mul_(c, b), mul_(mod_(sub_(d, mul_(mul_(a, mul_(d, a)), m)), m), b));
		lemma_eq_ref(b);
		cong_mul_(mod_(d, m), b, mod_(sub_(d, mul_(mul_(a, mul_(d, a)), m)), m), b);
		lemma_eq_ref(mul_(c, b));
	}
	let temp_54_0 = (mul_((sub_(b, (mod_(a, m)))), (add_(a, b))));
	let temp_54_1 = (mul_((add_(a, b)), (sub_(b, (mod_(a, m))))));
	assert(eq_(temp_54_0, temp_54_1)) by {
		lemma_mul_comm(sub_(b, mod_(a, m)), add_(a, b));
	}
	let temp_55_0 = (mul_((mul_(b, d)), (mul_(a, d))));
	let temp_55_1 = (mul_((mul_(d, b)), (mul_(a, d))));
	assert(eq_(temp_55_0, temp_55_1)) by {
		cong_mul_(mul_(b, d), mul_(a, d), mul_(d, b), mul_(a, d));
		lemma_mul_comm(b, d);
		lemma_eq_ref(mul_(a, d));
	}
	let temp_56_0 = (mul_((mul_((mod_(c, m)), b)), (mul_(as_elem(62), a))));
	let temp_56_1 = (mul_((mul_((mod_((sub_(c, (mul_((add_((mul_(b, b)), (mul_(d, c)))), m)))), m)), b)), (mul_(as_elem(62), a))));
	assert(eq_(temp_56_0, temp_56_1)) by {
		cong_mul_(mul_(mod_(c, m), b), mul_(as_elem(62), a), mul_(mod_(sub_(c, mul_(add_(mul_(b, b), mul_(d, c)), m)), m), b), mul_(as_elem(62), a));
		lemma_mod_mul_vanish(c, add_(mul_(b, b), mul_(d, c)), m);
		lemma_eq_ref(b);
		cong_mul_(mod_(c, m), b, mod_(sub_(c, mul_(add_(mul_(b, b), mul_(d, c)), m)), m), b);
		lemma_eq_ref(mul_(as_elem(62), a));
	}
	let temp_57_0 = (mod_((mul_((sub_(c, b)), (mul_(a, d)))), m));
	let temp_57_1 = (mod_((sub_((mul_(c, (mul_(a, d)))), (mul_(b, (mul_(a, d)))))), m));
	assert(eq_(temp_57_0, temp_57_1)) by {
		lemma_mul_dist(mul_(a, d), c, b);
		cong_mod_(mul_(sub_(c, b), mul_(a, d)), m, sub_(mul_(c, mul_(a, d)), mul_(b, mul_(a, d))), m);
		lemma_eq_ref(m);
	}
	let temp_58_0 = (mul_((add_(c, (mod_(c, m)))), (mul_(d, c))));
	let temp_58_1 = (mul_((add_(c, (mod_(c, m)))), (mul_(c, d))));
	assert(eq_(temp_58_0, temp_58_1)) by {
		cong_mul_(add_(c, mod_(c, m)), mul_(d, c), add_(c, mod_(c, m)), mul_(c, d));
		lemma_mul_comm(d, c);
		lemma_eq_ref(add_(c, mod_(c, m)));
	}
	let temp_59_0 = (mul_((mul_(b, d)), (sub_(c, d))));
	let temp_59_1 = (mul_((mul_(d, b)), (sub_(c, d))));
	assert(eq_(temp_59_0, temp_59_1)) by {
		cong_mul_(mul_(b, d), sub_(c, d), mul_(d, b), sub_(c, d));
		lemma_mul_comm(b, d);
		lemma_eq_ref(sub_(c, d));
	}
	let temp_60_0 = (mul_((mul_(a, (mod_(b, m)))), (sub_(a, a))));
	let temp_60_1 = (mul_((mul_(a, (mod_((add_(b, (mul_((mul_((mul_(a, d)), (mul_((mod_(a, m)), d)))), m)))), m)))), (sub_(a, a))));
	assert(eq_(temp_60_0, temp_60_1)) by {
		lemma_mod_mul_vanish(b, mul_(mul_(a, d), mul_(mod_(a, m), d)), m);
		cong_mul_(mul_(a, mod_(b, m)), sub_(a, a), mul_(a, mod_(add_(b, mul_(mul_(mul_(a, d), mul_(mod_(a, m), d)), m)), m)), sub_(a, a));
		lemma_eq_ref(a);
		cong_mul_(a, mod_(b, m), a, mod_(add_(b, mul_(mul_(mul_(a, d), mul_(mod_(a, m), d)), m)), m));
		lemma_eq_ref(sub_(a, a));
	}
	let temp_61_0 = (mul_((mul_(d, c)), (mul_(a, b))));
	let temp_61_1 = (mul_((mul_((mul_(d, c)), a)), b));
	assert(eq_(temp_61_0, temp_61_1)) by {
		lemma_mul_assoc(mul_(d, c), a, b);
	}
	let temp_62_0 = (mul_((add_((mod_(b, m)), b)), (mod_((mul_(c, (mod_(d, m)))), m))));
	let temp_62_1 = (mul_((add_((mod_(b, m)), b)), (mod_((mod_((mul_(d, c)), m)), m))));
	assert(eq_(temp_62_0, temp_62_1)) by {
		lemma_mod_mul_noop(d, c, m);
		cong_mul_(add_(mod_(b, m), b), mod_(mul_(c, mod_(d, m)), m), add_(mod_(b, m), b), mod_(mod_(mul_(d, c), m), m));
		lemma_eq_ref(add_(mod_(b, m), b));
		lemma_eq_sym(mod_(mod_(mul_(d, c), m), m), mod_(mul_(c, mod_(d, m)), m));
	}
	let temp_63_0 = (mul_((mul_((mod_(c, m)), d)), (sub_(b, c))));
	let temp_63_1 = (mul_((mul_(d, (mod_(c, m)))), (sub_(b, c))));
	assert(eq_(temp_63_0, temp_63_1)) by {
		lemma_mul_comm(mod_(c, m), d);
		cong_mul_(mul_(mod_(c, m), d), sub_(b, c), mul_(d, mod_(c, m)), sub_(b, c));
		lemma_eq_ref(sub_(b, c));
	}
	let temp_64_0 = (mul_((mul_(as_elem(4), d)), (mul_(b, d))));
	let temp_64_1 = (mul_((mul_(d, as_elem(4))), (mul_(b, d))));
	assert(eq_(temp_64_0, temp_64_1)) by {
		cong_mul_(mul_(as_elem(4), d), mul_(b, d), mul_(d, as_elem(4)), mul_(b, d));
		lemma_mul_comm(as_elem(4), d);
		lemma_eq_ref(mul_(b, d));
	}
	let temp_65_0 = (mul_((mul_(a, (mod_(as_elem(40), m)))), (add_(d, b))));
	let temp_65_1 = (mul_((add_(d, b)), (mul_(a, (mod_(as_elem(40), m))))));
	assert(eq_(temp_65_0, temp_65_1)) by {
		lemma_mul_comm(mul_(a, mod_(as_elem(40), m)), add_(d, b));
	}
	let temp_66_0 = (mul_((mul_(d, d)), (mul_(as_elem(38), b))));
	let temp_66_1 = (mul_((mul_(d, d)), (mul_(b, as_elem(38)))));
	assert(eq_(temp_66_0, temp_66_1)) by {
		cong_mul_(mul_(d, d), mul_(as_elem(38), b), mul_(d, d), mul_(b, as_elem(38)));
		lemma_mul_comm(d, d);
		lemma_mul_comm(as_elem(38), b);
	}
	let temp_67_0 = (mul_((mul_((mod_(c, m)), c)), (mul_(b, c))));
	let temp_67_1 = (mul_((mod_(c, m)), (mul_(c, (mul_(b, c))))));
	assert(eq_(temp_67_0, temp_67_1)) by {
		lemma_eq_sym(temp_67_1, temp_67_0);
		lemma_mul_assoc(mod_(c, m), c, mul_(b, c));
	}
	let temp_68_0 = (mul_((mod_((mul_(d, c)), m)), (mul_(d, a))));
	let temp_68_1 = (mul_((mul_((mod_((mul_(d, c)), m)), d)), a));
	assert(eq_(temp_68_0, temp_68_1)) by {
		lemma_mul_assoc(mod_(mul_(d, c), m), d, a);
	}
	let temp_69_0 = (add_((mul_(d, d)), (mul_(a, d))));
	let temp_69_1 = (add_((mul_(a, d)), (mul_(d, d))));
	assert(eq_(temp_69_0, temp_69_1)) by {
		lemma_add_comm(mul_(d, d), mul_(a, d));
	}
	let temp_70_0 = (mul_((sub_(a, b)), (mul_(b, as_elem(17)))));
	let temp_70_1 = (mul_((mul_(b, as_elem(17))), (sub_(a, b))));
	assert(eq_(temp_70_0, temp_70_1)) by {
		lemma_mul_comm(sub_(a, b), mul_(b, as_elem(17)));
	}
	let temp_71_0 = (sub_((mod_((mul_(c, d)), m)), (mul_(c, (mod_(d, m))))));
	let temp_71_1 = (sub_((mod_((mul_(d, c)), m)), (mul_(c, (mod_(d, m))))));
	assert(eq_(temp_71_0, temp_71_1)) by {
		lemma_mul_comm(c, d);
		cong_sub_(mod_(mul_(c, d), m), mul_(c, mod_(d, m)), mod_(mul_(d, c), m), mul_(c, mod_(d, m)));
		lemma_eq_ref(m);
		cong_mod_(mul_(c, d), m, mul_(d, c), m);
		lemma_eq_ref(mul_(c, mod_(d, m)));
	}
	let temp_72_0 = (sub_((add_(a, a)), (sub_(b, d))));
	let temp_72_1 = (sub_((add_(a, a)), (sub_(b, d))));
	assert(eq_(temp_72_0, temp_72_1)) by {
		lemma_eq_ref(temp_72_0);
	}
	let temp_73_0 = (mul_((add_(c, a)), (add_(d, a))));
	let temp_73_1 = (mul_((add_(c, a)), (add_(a, d))));
	assert(eq_(temp_73_0, temp_73_1)) by {
		cong_mul_(add_(c, a), add_(d, a), add_(c, a), add_(a, d));
		lemma_add_comm(d, a);
		lemma_eq_ref(add_(c, a));
	}
	let temp_74_0 = (mod_((mul_((mul_(d, (mod_(b, m)))), (mul_(d, c)))), m));
	let temp_74_1 = (mod_((mul_(d, (mul_((mod_(b, m)), (mul_(d, c)))))), m));
	assert(eq_(temp_74_0, temp_74_1)) by {
		lemma_mul_assoc(d, mod_(b, m), mul_(d, c));
		cong_mod_(mul_(mul_(d, mod_(b, m)), mul_(d, c)), m, mul_(d, mul_(mod_(b, m), mul_(d, c))), m);
		lemma_eq_sym(mul_(d, mul_(mod_(b, m), mul_(d, c))), mul_(mul_(d, mod_(b, m)), mul_(d, c)));
		lemma_eq_ref(m);
	}
	let temp_75_0 = (mul_((sub_(a, a)), (mod_((mul_(c, c)), m))));
	let temp_75_1 = (mul_((sub_(a, a)), (mod_((mul_(c, c)), m))));
	assert(eq_(temp_75_0, temp_75_1)) by {
		lemma_eq_ref(temp_75_0);
	}
	let temp_76_0 = (mul_((mul_(b, d)), (mul_(d, a))));
	let temp_76_1 = (mul_((mul_((mul_(b, d)), d)), a));
	assert(eq_(temp_76_0, temp_76_1)) by {
		lemma_mul_assoc(mul_(b, d), d, a);
	}
	let temp_77_0 = (mul_((mul_(a, b)), (add_(a, c))));
	let temp_77_1 = (add_((mul_((mul_(a, b)), a)), (mul_((mul_(a, b)), c))));
	assert(eq_(temp_77_0, temp_77_1)) by {
		lemma_mul_dist(mul_(a, b), a, c);
	}
	let temp_78_0 = (add_((mul_(b, c)), (mul_(d, as_elem(70)))));
	let temp_78_1 = (add_((mul_(d, as_elem(70))), (mul_(b, c))));
	assert(eq_(temp_78_0, temp_78_1)) by {
		lemma_add_comm(mul_(b, c), mul_(d, as_elem(70)));
	}
	let temp_79_0 = (mul_(b, (mul_(a, a))));
	let temp_79_1 = (mul_(b, (mul_(a, a))));
	assert(eq_(temp_79_0, temp_79_1)) by {
		lemma_eq_ref(temp_79_0);
	}
	let temp_80_0 = (mod_((mul_((mul_(d, b)), (sub_(as_elem(48), b)))), m));
	let temp_80_1 = (mod_((mul_(d, (mul_(b, (sub_(as_elem(48), b)))))), m));
	assert(eq_(temp_80_0, temp_80_1)) by {
		lemma_mul_assoc(d, b, sub_(as_elem(48), b));
		cong_mod_(mul_(mul_(d, b), sub_(as_elem(48), b)), m, mul_(d, mul_(b, sub_(as_elem(48), b))), m);
		lemma_eq_sym(mul_(d, mul_(b, sub_(as_elem(48), b))), mul_(mul_(d, b), sub_(as_elem(48), b)));
		lemma_eq_ref(m);
	}
	let temp_81_0 = (mul_((mul_(b, (mod_(a, m)))), (mul_(d, c))));
	let temp_81_1 = (mul_((mul_(b, (mod_((add_((mul_((add_((mod_((mul_(d, a)), m)), (mod_((mul_(b, d)), m)))), m)), a)), m)))), (mul_(d, c))));
	assert(eq_(temp_81_0, temp_81_1)) by {
		cong_mul_(b, mod_(a, m), b, mod_(add_(mul_(add_(mod_(mul_(d, a), m), mod_(mul_(b, d), m)), m), a), m));
		lemma_eq_ref(mul_(d, c));
		lemma_eq_ref(b);
		lemma_mod_mul_vanish(a, add_(mod_(mul_(d, a), m), mod_(mul_(b, d), m)), m);
		cong_mul_(mul_(b, mod_(a, m)), mul_(d, c), mul_(b, mod_(add_(mul_(add_(mod_(mul_(d, a), m), mod_(mul_(b, d), m)), m), a), m)), mul_(d, c));
	}
	let temp_82_0 = (mul_((mul_((mod_(c, m)), (mod_(d, m)))), (add_(c, (mod_(d, m))))));
	let temp_82_1 = (mul_((mul_((mod_(c, m)), (mod_((add_((mul_((mul_((mul_(b, d)), (mul_(d, (mod_(b, m)))))), m)), d)), m)))), (add_(c, (mod_(d, m))))));
	assert(eq_(temp_82_0, temp_82_1)) by {
		lemma_mod_mul_vanish(d, mul_(mul_(b, d), mul_(d, mod_(b, m))), m);
		cong_mul_(mul_(mod_(c, m), mod_(d, m)), add_(c, mod_(d, m)), mul_(mod_(c, m), mod_(add_(mul_(mul_(mul_(b, d), mul_(d, mod_(b, m))), m), d), m)), add_(c, mod_(d, m)));
		lemma_eq_ref(mod_(c, m));
		cong_mul_(mod_(c, m), mod_(d, m), mod_(c, m), mod_(add_(mul_(mul_(mul_(b, d), mul_(d, mod_(b, m))), m), d), m));
		lemma_eq_ref(add_(c, mod_(d, m)));
	}
	let temp_83_0 = (mul_((mul_(c, b)), (mul_(b, b))));
	let temp_83_1 = (mul_((mul_(b, b)), (mul_(c, b))));
	assert(eq_(temp_83_0, temp_83_1)) by {
		lemma_mul_comm(mul_(c, b), mul_(b, b));
	}
	let temp_84_0 = (mul_((mul_(a, a)), (mod_((add_(b, d)), m))));
	let temp_84_1 = (mul_((mul_(a, a)), (mod_((add_((mod_(b, m)), d)), m))));
	assert(eq_(temp_84_0, temp_84_1)) by {
		lemma_mul_comm(a, a);
		lemma_mod_add_noop(b, d, m);
		cong_mul_(mul_(a, a), mod_(add_(b, d), m), mul_(a, a), mod_(add_(mod_(b, m), d), m));
	}
	let temp_85_0 = (mul_(b, (add_(d, c))));
	let temp_85_1 = (add_((mul_(b, d)), (mul_(b, c))));
	assert(eq_(temp_85_0, temp_85_1)) by {
		lemma_mul_dist(b, d, c);
	}

}

} // verus!