use builtin_macros::*;
// use builtin::*;
mod nl_basics;
use crate::nl_basics::*;
verus! {

pub proof fn free_0(a: Elem, b: Elem, c: Elem, d: Elem, m: Elem)
{
	let temp_0_0 = (sub_((mod_((mul_(d, b)), m)), (mul_(d, d))));
	let temp_0_1 = (sub_((mod_((mul_(b, d)), m)), (mul_(d, d))));
	assert(eq_(temp_0_0, temp_0_1)) by {
		lemma_mul_comm(d, b);
		lemma_mul_comm(d, d);
		cong_sub_(mod_(mul_(d, b), m), mul_(d, d), mod_(mul_(b, d), m), mul_(d, d));
		cong_mod_(mul_(d, b), m, mul_(b, d), m);
		lemma_eq_ref(m);
	}
	let temp_1_0 = (mul_(d, (mul_(b, d))));
	let temp_1_1 = (mul_((mul_(b, d)), d));
	assert(eq_(temp_1_0, temp_1_1)) by {
		lemma_mul_comm(d, mul_(b, d));
	}
	let temp_2_0 = (mul_((mul_(b, d)), (mul_(d, d))));
	let temp_2_1 = (mul_((mul_(d, b)), (mul_(d, d))));
	assert(eq_(temp_2_0, temp_2_1)) by {
		cong_mul_(mul_(b, d), mul_(d, d), mul_(d, b), mul_(d, d));
		lemma_mul_comm(b, d);
		lemma_mul_comm(d, d);
	}
	let temp_3_0 = (sub_((mul_(a, (mod_(c, m)))), (mul_(d, d))));
	let temp_3_1 = (sub_((mul_((mod_(c, m)), a)), (mul_(d, d))));
	assert(eq_(temp_3_0, temp_3_1)) by {
		lemma_mul_comm(a, mod_(c, m));
		lemma_mul_comm(d, d);
		cong_sub_(mul_(a, mod_(c, m)), mul_(d, d), mul_(mod_(c, m), a), mul_(d, d));
	}
	let temp_4_0 = (mul_((mul_(a, (mod_(c, m)))), (mul_(b, b))));
	let temp_4_1 = (mul_((mul_(a, (mod_((sub_(c, (mul_((mul_((mul_(b, b)), (mod_((sub_(as_elem(20), b)), m)))), m)))), m)))), (mul_(b, b))));
	assert(eq_(temp_4_0, temp_4_1)) by {
		lemma_mul_comm(b, b);
		lemma_mod_mul_vanish(c, mul_(mul_(b, b), mod_(sub_(as_elem(20), b), m)), m);
		cong_mul_(mul_(a, mod_(c, m)), mul_(b, b), mul_(a, mod_(sub_(c, mul_(mul_(mul_(b, b), mod_(sub_(as_elem(20), b), m)), m)), m)), mul_(b, b));
		lemma_eq_ref(a);
		cong_mul_(a, mod_(c, m), a, mod_(sub_(c, mul_(mul_(mul_(b, b), mod_(sub_(as_elem(20), b), m)), m)), m));
	}
	let temp_5_0 = (mul_((add_(b, a)), (mul_((mod_(d, m)), d))));
	let temp_5_1 = (mul_((mul_((mod_(d, m)), d)), (add_(b, a))));
	assert(eq_(temp_5_0, temp_5_1)) by {
		lemma_mul_comm(add_(b, a), mul_(mod_(d, m), d));
	}
	let temp_6_0 = (mul_((mul_((mod_(d, m)), a)), (add_(d, (mod_(a, m))))));
	let temp_6_1 = (mul_((mul_((mod_(d, m)), a)), (add_(d, (mod_((add_(a, (mul_((mul_((mul_(b, a)), (mod_((mul_(a, a)), m)))), m)))), m))))));
	assert(eq_(temp_6_0, temp_6_1)) by {
		lemma_mod_mul_vanish(a, mul_(mul_(b, a), mod_(mul_(a, a), m)), m);
		cong_mul_(mul_(mod_(d, m), a), add_(d, mod_(a, m)), mul_(mod_(d, m), a), add_(d, mod_(add_(a, mul_(mul_(mul_(b, a), mod_(mul_(a, a), m)), m)), m)));
		lemma_eq_ref(mul_(mod_(d, m), a));
		cong_add_(d, mod_(a, m), d, mod_(add_(a, mul_(mul_(mul_(b, a), mod_(mul_(a, a), m)), m)), m));
		lemma_eq_ref(d);
	}
	let temp_7_0 = (mul_((mul_(b, b)), (mul_(d, c))));
	let temp_7_1 = (mul_((mul_(d, c)), (mul_(b, b))));
	assert(eq_(temp_7_0, temp_7_1)) by {
		lemma_mul_comm(mul_(b, b), mul_(d, c));
	}
	let temp_8_0 = (mul_((mod_((sub_(b, c)), m)), b));
	let temp_8_1 = (mul_(b, (mod_((sub_(b, c)), m))));
	assert(eq_(temp_8_0, temp_8_1)) by {
		lemma_mul_comm(mod_(sub_(b, c), m), b);
	}
	let temp_9_0 = (mod_((mul_((mul_(b, c)), (add_(d, (mod_(d, m)))))), m));
	let temp_9_1 = (mod_((mul_((mul_(c, b)), (add_(d, (mod_(d, m)))))), m));
	assert(eq_(temp_9_0, temp_9_1)) by {
		lemma_mul_comm(b, c);
		cong_mod_(mul_(mul_(b, c), add_(d, mod_(d, m))), m, mul_(mul_(c, b), add_(d, mod_(d, m))), m);
		lemma_eq_ref(add_(d, mod_(d, m)));
		cong_mul_(mul_(b, c), add_(d, mod_(d, m)), mul_(c, b), add_(d, mod_(d, m)));
		lemma_eq_ref(m);
	}
	let temp_10_0 = (mul_((mul_(d, (mod_(as_elem(68), m)))), (mod_((mul_((mod_(a, m)), d)), m))));
	let temp_10_1 = (mul_(d, (mul_((mod_(as_elem(68), m)), (mod_((mul_((mod_(a, m)), d)), m))))));
	assert(eq_(temp_10_0, temp_10_1)) by {
		lemma_mul_assoc(d, mod_(as_elem(68), m), mod_(mul_(mod_(a, m), d), m));
		lemma_eq_sym(temp_10_1, temp_10_0);
	}
	let temp_11_0 = (mul_((mul_(b, c)), (mul_((mod_(d, m)), a))));
	let temp_11_1 = (mul_((mul_(b, c)), (mul_((mod_((add_((mul_((mul_((mod_((mul_(a, c)), m)), (mul_(b, c)))), m)), d)), m)), a))));
	assert(eq_(temp_11_0, temp_11_1)) by {
		lemma_mod_mul_vanish(d, mul_(mod_(mul_(a, c), m), mul_(b, c)), m);
		cong_mul_(mul_(b, c), mul_(mod_(d, m), a), mul_(b, c), mul_(mod_(add_(mul_(mul_(mod_(mul_(a, c), m), mul_(b, c)), m), d), m), a));
		lemma_eq_ref(mul_(b, c));
		lemma_eq_ref(a);
		cong_mul_(mod_(d, m), a, mod_(add_(mul_(mul_(mod_(mul_(a, c), m), mul_(b, c)), m), d), m), a);
	}
	let temp_12_0 = (mod_((mul_((mul_(b, c)), (mul_(b, a)))), m));
	let temp_12_1 = (mod_((add_((mul_((mul_(b, c)), (mul_(b, a)))), (mul_((mul_((mul_(b, b)), (mul_(c, d)))), m)))), m));
	assert(eq_(temp_12_0, temp_12_1)) by {
		lemma_mod_mul_vanish(mul_(mul_(b, c), mul_(b, a)), mul_(mul_(b, b), mul_(c, d)), m);
	}
	let temp_13_0 = (mul_((mul_(d, d)), (mul_((mod_(b, m)), d))));
	let temp_13_1 = (mul_((mul_((mod_(b, m)), d)), (mul_(d, d))));
	assert(eq_(temp_13_0, temp_13_1)) by {
		lemma_mul_comm(mul_(d, d), mul_(mod_(b, m), d));
	}
	let temp_14_0 = (mul_((add_(c, b)), (mod_((mul_(c, d)), m))));
	let temp_14_1 = (mul_((add_(c, b)), (mod_((add_((mul_((mul_(b, (mul_((mod_(c, m)), d)))), m)), (mul_(c, d)))), m))));
	assert(eq_(temp_14_0, temp_14_1)) by {
		lemma_mod_mul_vanish(mul_(c, d), mul_(b, mul_(mod_(c, m), d)), m);
		cong_mul_(add_(c, b), mod_(mul_(c, d), m), add_(c, b), mod_(add_(mul_(mul_(b, mul_(mod_(c, m), d)), m), mul_(c, d)), m));
		lemma_eq_ref(add_(c, b));
	}
	let temp_15_0 = (mul_((mul_(c, a)), (mul_((mod_(b, m)), c))));
	let temp_15_1 = (mul_((mul_((mod_(b, m)), c)), (mul_(c, a))));
	assert(eq_(temp_15_0, temp_15_1)) by {
		lemma_mul_comm(mul_(c, a), mul_(mod_(b, m), c));
	}
	let temp_16_0 = (mul_((add_(d, as_elem(42))), (mul_(c, a))));
	let temp_16_1 = (add_((mul_(d, (mul_(c, a)))), (mul_(as_elem(42), (mul_(c, a))))));
	assert(eq_(temp_16_0, temp_16_1)) by {
		lemma_mul_dist(d, as_elem(42), mul_(c, a));
	}
	let temp_17_0 = (sub_((mul_(a, c)), (mul_(a, b))));
	let temp_17_1 = (sub_((mul_(c, a)), (mul_(a, b))));
	assert(eq_(temp_17_0, temp_17_1)) by {
		cong_sub_(mul_(a, c), mul_(a, b), mul_(c, a), mul_(a, b));
		lemma_mul_comm(a, c);
		lemma_eq_ref(mul_(a, b));
	}
	let temp_18_0 = (mul_((mod_((add_(c, a)), m)), (mul_(d, a))));
	let temp_18_1 = (mul_((mod_((add_((mod_(c, m)), (mod_(a, m)))), m)), (mul_(d, a))));
	assert(eq_(temp_18_0, temp_18_1)) by {
		lemma_mod_add_noop(c, a, m);
		cong_mul_(mod_(add_(c, a), m), mul_(d, a), mod_(add_(mod_(c, m), mod_(a, m)), m), mul_(d, a));
		lemma_eq_ref(mul_(d, a));
	}
	let temp_19_0 = (add_((mul_(b, c)), (mul_(b, b))));
	let temp_19_1 = (add_((mul_(b, b)), (mul_(b, c))));
	assert(eq_(temp_19_0, temp_19_1)) by {
		lemma_add_comm(mul_(b, c), mul_(b, b));
	}
	let temp_20_0 = (add_((mul_(a, d)), (mul_(b, d))));
	let temp_20_1 = (add_((mul_(d, a)), (mul_(b, d))));
	assert(eq_(temp_20_0, temp_20_1)) by {
		cong_add_(mul_(a, d), mul_(b, d), mul_(d, a), mul_(b, d));
		lemma_mul_comm(a, d);
		lemma_eq_ref(mul_(b, d));
	}
	let temp_21_0 = (sub_((mul_(d, a)), (mul_((mod_(d, m)), a))));
	let temp_21_1 = (sub_((mul_(a, d)), (mul_((mod_(d, m)), a))));
	assert(eq_(temp_21_0, temp_21_1)) by {
		cong_sub_(mul_(d, a), mul_(mod_(d, m), a), mul_(a, d), mul_(mod_(d, m), a));
		lemma_mul_comm(d, a);
		lemma_eq_ref(mul_(mod_(d, m), a));
	}
	let temp_22_0 = (mul_((mod_((add_((mod_(c, m)), c)), m)), (mod_((mul_(a, a)), m))));
	let temp_22_1 = (mul_((mod_((add_(c, (mod_(c, m)))), m)), (mod_((mul_(a, a)), m))));
	assert(eq_(temp_22_0, temp_22_1)) by {
		lemma_add_comm(mod_(c, m), c);
		cong_mul_(mod_(add_(mod_(c, m), c), m), mod_(mul_(a, a), m), mod_(add_(c, mod_(c, m)), m), mod_(mul_(a, a), m));
		cong_mod_(add_(mod_(c, m), c), m, add_(c, mod_(c, m)), m);
		lemma_eq_ref(m);
		lemma_eq_ref(mod_(mul_(a, a), m));
	}
	let temp_23_0 = (mul_((mul_(d, b)), (sub_(d, c))));
	let temp_23_1 = (mul_(d, (mul_(b, (sub_(d, c))))));
	assert(eq_(temp_23_0, temp_23_1)) by {
		lemma_eq_sym(temp_23_1, temp_23_0);
		lemma_mul_assoc(d, b, sub_(d, c));
	}
	let temp_24_0 = (sub_((mul_(c, c)), (mod_((mul_(a, a)), m))));
	let temp_24_1 = (sub_((mul_(c, c)), (mod_((sub_((mul_(a, a)), (mul_((mul_((mul_(a, b)), (mul_(d, d)))), m)))), m))));
	assert(eq_(temp_24_0, temp_24_1)) by {
		lemma_mul_comm(c, c);
		lemma_mod_mul_vanish(mul_(a, a), mul_(mul_(a, b), mul_(d, d)), m);
		cong_sub_(mul_(c, c), mod_(mul_(a, a), m), mul_(c, c), mod_(sub_(mul_(a, a), mul_(mul_(mul_(a, b), mul_(d, d)), m)), m));
	}
	let temp_25_0 = (mul_((mul_(c, a)), (mul_(a, a))));
	let temp_25_1 = (mul_((mul_(a, c)), (mul_(a, a))));
	assert(eq_(temp_25_0, temp_25_1)) by {
		cong_mul_(mul_(c, a), mul_(a, a), mul_(a, c), mul_(a, a));
		lemma_mul_comm(c, a);
		lemma_mul_comm(a, a);
	}
	let temp_26_0 = (sub_((mod_((mul_(c, b)), m)), as_elem(78)));
	let temp_26_1 = (sub_((mod_((mul_(b, c)), m)), as_elem(78)));
	assert(eq_(temp_26_0, temp_26_1)) by {
		lemma_mul_comm(c, b);
		cong_sub_(mod_(mul_(c, b), m), as_elem(78), mod_(mul_(b, c), m), as_elem(78));
		cong_mod_(mul_(c, b), m, mul_(b, c), m);
		lemma_eq_ref(as_elem(78));
		lemma_eq_ref(m);
	}
	let temp_27_0 = (mul_((add_(b, b)), (mul_(d, c))));
	let temp_27_1 = (mul_((add_(b, b)), (mul_(c, d))));
	assert(eq_(temp_27_0, temp_27_1)) by {
		cong_mul_(add_(b, b), mul_(d, c), add_(b, b), mul_(c, d));
		lemma_add_comm(b, b);
		lemma_mul_comm(d, c);
	}
	let temp_28_0 = (sub_((mul_(b, d)), (mul_(b, (mod_(a, m))))));
	let temp_28_1 = (sub_((mul_(b, d)), (mul_((mod_(a, m)), b))));
	assert(eq_(temp_28_0, temp_28_1)) by {
		lemma_mul_comm(b, mod_(a, m));
		cong_sub_(mul_(b, d), mul_(b, mod_(a, m)), mul_(b, d), mul_(mod_(a, m), b));
		lemma_eq_ref(mul_(b, d));
	}
	let temp_29_0 = (mod_((mul_((mul_(b, b)), (add_(a, b)))), m));
	let temp_29_1 = (mod_((add_((mul_((mul_(b, b)), a)), (mul_((mul_(b, b)), b)))), m));
	assert(eq_(temp_29_0, temp_29_1)) by {
		lemma_mul_dist(mul_(b, b), a, b);
		cong_mod_(mul_(mul_(b, b), add_(a, b)), m, add_(mul_(mul_(b, b), a), mul_(mul_(b, b), b)), m);
		lemma_eq_ref(m);
	}
	let temp_30_0 = (mul_((mul_(d, d)), (sub_((mod_(d, m)), a))));
	let temp_30_1 = (mul_(d, (mul_(d, (sub_((mod_(d, m)), a))))));
	assert(eq_(temp_30_0, temp_30_1)) by {
		lemma_eq_sym(temp_30_1, temp_30_0);
		lemma_mul_assoc(d, d, sub_(mod_(d, m), a));
	}
	let temp_31_0 = (mul_((mul_(b, b)), d));
	let temp_31_1 = (mul_((mul_(b, b)), d));
	assert(eq_(temp_31_0, temp_31_1)) by {
		lemma_eq_ref(temp_31_0);
	}
	let temp_32_0 = (sub_((mul_(c, b)), (add_(b, a))));
	let temp_32_1 = (sub_((mul_(b, c)), (add_(b, a))));
	assert(eq_(temp_32_0, temp_32_1)) by {
		cong_sub_(mul_(c, b), add_(b, a), mul_(b, c), add_(b, a));
		lemma_mul_comm(c, b);
		lemma_eq_ref(add_(b, a));
	}
	let temp_33_0 = (mul_((mul_(d, d)), (mod_((mul_(b, a)), m))));
	let temp_33_1 = (mul_(d, (mul_(d, (mod_((mul_(b, a)), m))))));
	assert(eq_(temp_33_0, temp_33_1)) by {
		lemma_mul_assoc(d, d, mod_(mul_(b, a), m));
		lemma_eq_sym(temp_33_1, temp_33_0);
	}
	let temp_34_0 = (mul_((mul_(d, b)), (mod_((mul_((mod_(a, m)), b)), m))));
	let temp_34_1 = (mul_((mul_(d, b)), (mod_((mul_((mod_((add_(a, (mul_((mod_((mul_((mul_(c, c)), (mul_(c, a)))), m)), m)))), m)), b)), m))));
	assert(eq_(temp_34_0, temp_34_1)) by {
		lemma_mod_mul_vanish(a, mod_(mul_(mul_(c, c), mul_(c, a)), m), m);
		cong_mul_(mul_(d, b), mod_(mul_(mod_(a, m), b), m), mul_(d, b), mod_(mul_(mod_(add_(a, mul_(mod_(mul_(mul_(c, c), mul_(c, a)), m), m)), m), b), m));
		cong_mod_(mul_(mod_(a, m), b), m, mul_(mod_(add_(a, mul_(mod_(mul_(mul_(c, c), mul_(c, a)), m), m)), m), b), m);
		lemma_eq_ref(m);
		cong_mul_(mod_(a, m), b, mod_(add_(a, mul_(mod_(mul_(mul_(c, c), mul_(c, a)), m), m)), m), b);
		lemma_eq_ref(b);
		lemma_eq_ref(mul_(d, b));
	}
	let temp_35_0 = (mul_((mul_(b, c)), (mul_(d, c))));
	let temp_35_1 = (mul_((mul_((mul_(b, c)), d)), c));
	assert(eq_(temp_35_0, temp_35_1)) by {
		lemma_mul_assoc(mul_(b, c), d, c);
	}
	let temp_36_0 = (mul_((mul_(a, c)), (mul_(c, c))));
	let temp_36_1 = (mul_(a, (mul_(c, (mul_(c, c))))));
	assert(eq_(temp_36_0, temp_36_1)) by {
		lemma_eq_sym(temp_36_1, temp_36_0);
		lemma_mul_assoc(a, c, mul_(c, c));
	}
	let temp_37_0 = (mul_((mul_((mod_(d, m)), b)), (add_(a, c))));
	let temp_37_1 = (add_((mul_((mul_((mod_(d, m)), b)), a)), (mul_((mul_((mod_(d, m)), b)), c))));
	assert(eq_(temp_37_0, temp_37_1)) by {
		lemma_mul_dist(mul_(mod_(d, m), b), a, c);
	}
	let temp_38_0 = (mul_((mul_(a, c)), (sub_(d, b))));
	let temp_38_1 = (mul_((sub_(d, b)), (mul_(a, c))));
	assert(eq_(temp_38_0, temp_38_1)) by {
		lemma_mul_comm(mul_(a, c), sub_(d, b));
	}
	let temp_39_0 = (add_((mul_(c, c)), (mul_(c, b))));
	let temp_39_1 = (add_((mul_(c, c)), (mul_(b, c))));
	assert(eq_(temp_39_0, temp_39_1)) by {
		cong_add_(mul_(c, c), mul_(c, b), mul_(c, c), mul_(b, c));
		lemma_mul_comm(c, b);
		lemma_eq_ref(mul_(c, c));
	}
	let temp_40_0 = (mul_((mul_(c, c)), (mul_(c, c))));
	let temp_40_1 = (mul_(c, (mul_(c, (mul_(c, c))))));
	assert(eq_(temp_40_0, temp_40_1)) by {
		lemma_eq_sym(temp_40_1, temp_40_0);
		lemma_mul_assoc(c, c, mul_(c, c));
	}
	let temp_41_0 = (mul_((mul_(d, b)), (add_(as_elem(38), c))));
	let temp_41_1 = (mul_((mul_(b, d)), (add_(as_elem(38), c))));
	assert(eq_(temp_41_0, temp_41_1)) by {
		lemma_mul_comm(d, b);
		cong_mul_(mul_(d, b), add_(as_elem(38), c), mul_(b, d), add_(as_elem(38), c));
		lemma_eq_ref(add_(as_elem(38), c));
	}
	let temp_42_0 = (add_((mul_(d, c)), (mul_(d, d))));
	let temp_42_1 = (mul_(d, (add_(c, d))));
	assert(eq_(temp_42_0, temp_42_1)) by {
		lemma_eq_sym(temp_42_1, temp_42_0);
		lemma_mul_dist(d, c, d);
	}
	let temp_43_0 = (mul_((mul_(d, a)), (mul_(a, c))));
	let temp_43_1 = (mul_((mul_((mul_(d, a)), a)), c));
	assert(eq_(temp_43_0, temp_43_1)) by {
		lemma_mul_assoc(mul_(d, a), a, c);
	}
	let temp_44_0 = (sub_((mul_(b, c)), (mul_(d, d))));
	let temp_44_1 = (sub_((mul_(b, c)), (mul_(d, d))));
	assert(eq_(temp_44_0, temp_44_1)) by {
		lemma_eq_ref(temp_44_0);
	}
	let temp_45_0 = (mul_((sub_(a, as_elem(90))), (mul_(d, b))));
	let temp_45_1 = (sub_((mul_(a, (mul_(d, b)))), (mul_(as_elem(90), (mul_(d, b))))));
	assert(eq_(temp_45_0, temp_45_1)) by {
		lemma_mul_dist(mul_(d, b), a, as_elem(90));
	}
	let temp_46_0 = (mul_((mod_((mul_(d, a)), m)), (mul_(d, c))));
	let temp_46_1 = (mul_((mod_((add_((mul_(d, a)), (mul_((add_((mul_((mod_(c, m)), a)), (mod_((mul_(b, a)), m)))), m)))), m)), (mul_(d, c))));
	assert(eq_(temp_46_0, temp_46_1)) by {
		lemma_mod_mul_vanish(mul_(d, a), add_(mul_(mod_(c, m), a), mod_(mul_(b, a), m)), m);
		cong_mul_(mod_(mul_(d, a), m), mul_(d, c), mod_(add_(mul_(d, a), mul_(add_(mul_(mod_(c, m), a), mod_(mul_(b, a), m)), m)), m), mul_(d, c));
		lemma_eq_ref(mul_(d, c));
	}
	let temp_47_0 = (mul_((sub_(c, c)), (mul_(as_elem(61), b))));
	let temp_47_1 = (mul_((mul_((sub_(c, c)), as_elem(61))), b));
	assert(eq_(temp_47_0, temp_47_1)) by {
		lemma_mul_assoc(sub_(c, c), as_elem(61), b);
	}
	let temp_48_0 = (mul_((mul_(b, a)), (add_(b, d))));
	let temp_48_1 = (mul_((mul_(a, b)), (add_(b, d))));
	assert(eq_(temp_48_0, temp_48_1)) by {
		cong_mul_(mul_(b, a), add_(b, d), mul_(a, b), add_(b, d));
		lemma_mul_comm(b, a);
		lemma_eq_ref(add_(b, d));
	}
	let temp_49_0 = (mul_((mul_(a, a)), (mul_(c, c))));
	let temp_49_1 = (mul_((mul_(a, a)), (mul_(c, c))));
	assert(eq_(temp_49_0, temp_49_1)) by {
		lemma_eq_ref(temp_49_0);
	}
	let temp_50_0 = (mul_((mul_(b, d)), (add_(c, (mod_(d, m))))));
	let temp_50_1 = (add_((mul_((mul_(b, d)), c)), (mul_((mul_(b, d)), (mod_(d, m))))));
	assert(eq_(temp_50_0, temp_50_1)) by {
		lemma_mul_dist(mul_(b, d), c, mod_(d, m));
	}
	let temp_51_0 = (mul_((mul_(c, a)), (mul_(c, b))));
	let temp_51_1 = (mul_((mul_((mul_(c, a)), c)), b));
	assert(eq_(temp_51_0, temp_51_1)) by {
		lemma_mul_assoc(mul_(c, a), c, b);
	}
	let temp_52_0 = (mul_((mul_((mod_(c, m)), d)), (mul_(c, a))));
	let temp_52_1 = (mul_((mul_((mul_((mod_(c, m)), d)), c)), a));
	assert(eq_(temp_52_0, temp_52_1)) by {
		lemma_mul_assoc(mul_(mod_(c, m), d), c, a);
	}
	let temp_53_0 = (sub_((mul_(b, c)), (mul_(a, d))));
	let temp_53_1 = (sub_((mul_(b, c)), (mul_(d, a))));
	assert(eq_(temp_53_0, temp_53_1)) by {
		cong_sub_(mul_(b, c), mul_(a, d), mul_(b, c), mul_(d, a));
		lemma_mul_comm(a, d);
		lemma_eq_ref(mul_(b, c));
	}
	let temp_54_0 = (sub_((sub_(d, (mod_(c, m)))), (mul_(a, as_elem(57)))));
	let temp_54_1 = (sub_((sub_(d, (mod_(c, m)))), (mul_(as_elem(57), a))));
	assert(eq_(temp_54_0, temp_54_1)) by {
		lemma_mul_comm(a, as_elem(57));
		cong_sub_(sub_(d, mod_(c, m)), mul_(a, as_elem(57)), sub_(d, mod_(c, m)), mul_(as_elem(57), a));
		lemma_eq_ref(sub_(d, mod_(c, m)));
	}
	let temp_55_0 = (mul_((mul_(d, d)), (mul_(a, c))));
	let temp_55_1 = (mul_(d, (mul_(d, (mul_(a, c))))));
	assert(eq_(temp_55_0, temp_55_1)) by {
		lemma_eq_sym(temp_55_1, temp_55_0);
		lemma_mul_assoc(d, d, mul_(a, c));
	}
	let temp_56_0 = (mul_(c, a));
	let temp_56_1 = (mul_(a, c));
	assert(eq_(temp_56_0, temp_56_1)) by {
		lemma_mul_comm(c, a);
	}
	let temp_57_0 = (mul_((mul_(b, d)), (mul_(b, (mod_(as_elem(45), m))))));
	let temp_57_1 = (mul_(b, (mul_(d, (mul_(b, (mod_(as_elem(45), m))))))));
	assert(eq_(temp_57_0, temp_57_1)) by {
		lemma_mul_assoc(b, d, mul_(b, mod_(as_elem(45), m)));
		lemma_eq_sym(temp_57_1, temp_57_0);
	}
	let temp_58_0 = (mul_((mod_((mul_((mod_(d, m)), (mod_(a, m)))), m)), (sub_(b, d))));
	let temp_58_1 = (mul_((mod_((mul_((mod_((add_((mul_((sub_((mod_((mul_(b, c)), m)), (add_(a, a)))), m)), d)), m)), (mod_(a, m)))), m)), (sub_(b, d))));
	assert(eq_(temp_58_0, temp_58_1)) by {
		cong_mul_(mod_(mul_(mod_(d, m), mod_(a, m)), m), sub_(b, d), mod_(mul_(mod_(add_(mul_(sub_(mod_(mul_(b, c), m), add_(a, a)), m), d), m), mod_(a, m)), m), sub_(b, d));
		lemma_mod_mul_vanish(d, sub_(mod_(mul_(b, c), m), add_(a, a)), m);
		cong_mod_(mul_(mod_(d, m), mod_(a, m)), m, mul_(mod_(add_(mul_(sub_(mod_(mul_(b, c), m), add_(a, a)), m), d), m), mod_(a, m)), m);
		lemma_eq_ref(sub_(b, d));
		lemma_eq_ref(mod_(a, m));
		cong_mul_(mod_(d, m), mod_(a, m), mod_(add_(mul_(sub_(mod_(mul_(b, c), m), add_(a, a)), m), d), m), mod_(a, m));
		lemma_eq_ref(m);
	}
	let temp_59_0 = (add_((mul_(d, c)), (mul_(b, c))));
	let temp_59_1 = (add_((mul_(b, c)), (mul_(d, c))));
	assert(eq_(temp_59_0, temp_59_1)) by {
		lemma_add_comm(mul_(d, c), mul_(b, c));
	}
	let temp_60_0 = (mod_((mul_((mul_(c, b)), (mul_(d, a)))), m));
	let temp_60_1 = (mod_((mul_((mul_(c, b)), (mul_(a, d)))), m));
	assert(eq_(temp_60_0, temp_60_1)) by {
		lemma_mul_comm(d, a);
		cong_mod_(mul_(mul_(c, b), mul_(d, a)), m, mul_(mul_(c, b), mul_(a, d)), m);
		lemma_eq_ref(mul_(c, b));
		cong_mul_(mul_(c, b), mul_(d, a), mul_(c, b), mul_(a, d));
		lemma_eq_ref(m);
	}
	let temp_61_0 = (mul_((mul_(a, as_elem(99))), (mul_(b, a))));
	let temp_61_1 = (mul_((mul_(as_elem(99), a)), (mul_(b, a))));
	assert(eq_(temp_61_0, temp_61_1)) by {
		cong_mul_(mul_(a, as_elem(99)), mul_(b, a), mul_(as_elem(99), a), mul_(b, a));
		lemma_mul_comm(a, as_elem(99));
		lemma_eq_ref(mul_(b, a));
	}
	let temp_62_0 = (mul_((add_(d, d)), (mul_(b, (mod_(a, m))))));
	let temp_62_1 = (mul_((mul_((add_(d, d)), b)), (mod_(a, m))));
	assert(eq_(temp_62_0, temp_62_1)) by {
		lemma_mul_assoc(add_(d, d), b, mod_(a, m));
	}
	let temp_63_0 = (mul_((mul_(b, b)), (add_(a, a))));
	let temp_63_1 = (mul_((add_(a, a)), (mul_(b, b))));
	assert(eq_(temp_63_0, temp_63_1)) by {
		lemma_mul_comm(mul_(b, b), add_(a, a));
	}
	let temp_64_0 = (mul_((mul_(d, c)), (mul_(a, a))));
	let temp_64_1 = (mul_((mul_((mul_(d, c)), a)), a));
	assert(eq_(temp_64_0, temp_64_1)) by {
		lemma_mul_assoc(mul_(d, c), a, a);
	}
	let temp_65_0 = (mul_((mod_((add_(c, c)), m)), (add_(d, a))));
	let temp_65_1 = (mul_((add_(d, a)), (mod_((add_(c, c)), m))));
	assert(eq_(temp_65_0, temp_65_1)) by {
		lemma_mul_comm(mod_(add_(c, c), m), add_(d, a));
	}
	let temp_66_0 = (mul_((mod_((mul_(d, d)), m)), (mul_(d, b))));
	let temp_66_1 = (mul_((mul_(d, b)), (mod_((mul_(d, d)), m))));
	assert(eq_(temp_66_0, temp_66_1)) by {
		lemma_mul_comm(mod_(mul_(d, d), m), mul_(d, b));
	}
	let temp_67_0 = (sub_((mul_(c, b)), (mul_(d, a))));
	let temp_67_1 = (sub_((mul_(c, b)), (mul_(a, d))));
	assert(eq_(temp_67_0, temp_67_1)) by {
		cong_sub_(mul_(c, b), mul_(d, a), mul_(c, b), mul_(a, d));
		lemma_mul_comm(d, a);
		lemma_eq_ref(mul_(c, b));
	}
	let temp_68_0 = (mul_((mul_(b, c)), (mul_(d, c))));
	let temp_68_1 = (mul_((mul_(d, c)), (mul_(b, c))));
	assert(eq_(temp_68_0, temp_68_1)) by {
		lemma_mul_comm(mul_(b, c), mul_(d, c));
	}
	let temp_69_0 = (mul_((mul_(b, b)), (mul_(b, d))));
	let temp_69_1 = (mul_(b, (mul_(b, (mul_(b, d))))));
	assert(eq_(temp_69_0, temp_69_1)) by {
		lemma_eq_sym(temp_69_1, temp_69_0);
		lemma_mul_assoc(b, b, mul_(b, d));
	}
	let temp_70_0 = (add_((sub_(a, d)), (mul_((mod_(b, m)), c))));
	let temp_70_1 = (add_((sub_(a, d)), (mul_((mod_((sub_(b, (mul_((sub_((mul_(c, d)), (mul_(c, a)))), m)))), m)), c))));
	assert(eq_(temp_70_0, temp_70_1)) by {
		lemma_mod_mul_vanish(b, sub_(mul_(c, d), mul_(c, a)), m);
		cong_add_(sub_(a, d), mul_(mod_(b, m), c), sub_(a, d), mul_(mod_(sub_(b, mul_(sub_(mul_(c, d), mul_(c, a)), m)), m), c));
		lemma_eq_ref(c);
		cong_mul_(mod_(b, m), c, mod_(sub_(b, mul_(sub_(mul_(c, d), mul_(c, a)), m)), m), c);
		lemma_eq_ref(sub_(a, d));
	}
	let temp_71_0 = (mul_((mod_((mul_(d, d)), m)), (mul_(d, b))));
	let temp_71_1 = (mul_((mod_((add_((mul_((mul_((mul_(d, d)), (mul_(d, (mod_(c, m)))))), m)), (mul_(d, d)))), m)), (mul_(d, b))));
	assert(eq_(temp_71_0, temp_71_1)) by {
		lemma_mod_mul_vanish(mul_(d, d), mul_(mul_(d, d), mul_(d, mod_(c, m))), m);
		cong_mul_(mod_(mul_(d, d), m), mul_(d, b), mod_(add_(mul_(mul_(mul_(d, d), mul_(d, mod_(c, m))), m), mul_(d, d)), m), mul_(d, b));
		lemma_eq_ref(mul_(d, b));
	}
	let temp_72_0 = (mul_((mod_((mul_(d, (mod_(c, m)))), m)), (add_((mod_(d, m)), b))));
	let temp_72_1 = (mul_((mod_((mod_((mul_(c, d)), m)), m)), (add_((mod_(d, m)), b))));
	assert(eq_(temp_72_0, temp_72_1)) by {
		lemma_mod_mul_noop(c, d, m);
		cong_mul_(mod_(mul_(d, mod_(c, m)), m), add_(mod_(d, m), b), mod_(mod_(mul_(c, d), m), m), add_(mod_(d, m), b));
		lemma_eq_sym(mod_(mod_(mul_(c, d), m), m), mod_(mul_(d, mod_(c, m)), m));
		lemma_eq_ref(add_(mod_(d, m), b));
	}
	let temp_73_0 = (sub_((mul_(c, b)), (mod_((mul_(as_elem(55), d)), m))));
	let temp_73_1 = (sub_((mul_(c, b)), (mod_((add_((mul_((mul_((mul_(as_elem(69), c)), (mul_(d, (mod_(d, m)))))), m)), (mul_(as_elem(55), d)))), m))));
	assert(eq_(temp_73_0, temp_73_1)) by {
		lemma_mod_mul_vanish(mul_(as_elem(55), d), mul_(mul_(as_elem(69), c), mul_(d, mod_(d, m))), m);
		cong_sub_(mul_(c, b), mod_(mul_(as_elem(55), d), m), mul_(c, b), mod_(add_(mul_(mul_(mul_(as_elem(69), c), mul_(d, mod_(d, m))), m), mul_(as_elem(55), d)), m));
		lemma_eq_ref(mul_(c, b));
	}
	let temp_74_0 = (mod_((mul_((sub_(c, a)), (mul_((mod_(a, m)), b)))), m));
	let temp_74_1 = (mod_((mul_((mul_((sub_(c, a)), (mod_(a, m)))), b)), m));
	assert(eq_(temp_74_0, temp_74_1)) by {
		lemma_mul_assoc(sub_(c, a), mod_(a, m), b);
		cong_mod_(mul_(sub_(c, a), mul_(mod_(a, m), b)), m, mul_(mul_(sub_(c, a), mod_(a, m)), b), m);
		lemma_eq_ref(m);
	}
	let temp_75_0 = (mul_((mod_((add_(c, (mod_(d, m)))), m)), (mul_(b, (mod_(a, m))))));
	let temp_75_1 = (mul_((mod_((add_((mul_((mod_((mul_((mod_((sub_(a, a)), m)), (mul_(a, as_elem(1))))), m)), m)), (add_(c, (mod_(d, m)))))), m)), (mul_(b, (mod_(a, m))))));
	assert(eq_(temp_75_0, temp_75_1)) by {
		cong_mul_(mod_(add_(c, mod_(d, m)), m), mul_(b, mod_(a, m)), mod_(add_(mul_(mod_(mul_(mod_(sub_(a, a), m), mul_(a, as_elem(1))), m), m), add_(c, mod_(d, m))), m), mul_(b, mod_(a, m)));
		lemma_mod_mul_vanish(add_(c, mod_(d, m)), mod_(mul_(mod_(sub_(a, a), m), mul_(a, as_elem(1))), m), m);
		lemma_eq_ref(mul_(b, mod_(a, m)));
	}
	let temp_76_0 = (mul_((add_(c, (mod_(b, m)))), (mul_(as_elem(76), (mod_(a, m))))));
	let temp_76_1 = (mul_((mul_(as_elem(76), (mod_(a, m)))), (add_(c, (mod_(b, m))))));
	assert(eq_(temp_76_0, temp_76_1)) by {
		lemma_mul_comm(add_(c, mod_(b, m)), mul_(as_elem(76), mod_(a, m)));
	}
	let temp_77_0 = (mul_((mul_(d, a)), (mul_(c, c))));
	let temp_77_1 = (mul_((mul_(c, c)), (mul_(d, a))));
	assert(eq_(temp_77_0, temp_77_1)) by {
		lemma_mul_comm(mul_(d, a), mul_(c, c));
	}
	let temp_78_0 = (mod_((mul_((mul_(a, a)), (mul_(b, (mod_(a, m)))))), m));
	let temp_78_1 = (mod_((mul_(a, (mul_(a, (mul_(b, (mod_(a, m)))))))), m));
	assert(eq_(temp_78_0, temp_78_1)) by {
		lemma_mul_assoc(a, a, mul_(b, mod_(a, m)));
		cong_mod_(mul_(mul_(a, a), mul_(b, mod_(a, m))), m, mul_(a, mul_(a, mul_(b, mod_(a, m)))), m);
		lemma_eq_ref(m);
		lemma_eq_sym(mul_(a, mul_(a, mul_(b, mod_(a, m)))), mul_(mul_(a, a), mul_(b, mod_(a, m))));
	}
	let temp_79_0 = (sub_((mul_(a, d)), (mul_(d, c))));
	let temp_79_1 = (sub_((mul_(a, d)), (mul_(c, d))));
	assert(eq_(temp_79_0, temp_79_1)) by {
		cong_sub_(mul_(a, d), mul_(d, c), mul_(a, d), mul_(c, d));
		lemma_mul_comm(d, c);
		lemma_eq_ref(mul_(a, d));
	}
	let temp_80_0 = (add_((mul_(b, a)), (mul_(b, b))));
	let temp_80_1 = (add_((mul_(b, b)), (mul_(b, a))));
	assert(eq_(temp_80_0, temp_80_1)) by {
		lemma_add_comm(mul_(b, a), mul_(b, b));
	}
	let temp_81_0 = (mul_((mul_(c, b)), (mul_(a, (mod_(a, m))))));
	let temp_81_1 = (mul_((mul_((mul_(c, b)), a)), (mod_(a, m))));
	assert(eq_(temp_81_0, temp_81_1)) by {
		lemma_mul_assoc(mul_(c, b), a, mod_(a, m));
	}
	let temp_82_0 = (mul_((mul_(c, c)), (mul_(b, b))));
	let temp_82_1 = (mul_(c, (mul_(c, (mul_(b, b))))));
	assert(eq_(temp_82_0, temp_82_1)) by {
		lemma_eq_sym(temp_82_1, temp_82_0);
		lemma_mul_assoc(c, c, mul_(b, b));
	}
	let temp_83_0 = (mul_((mul_(d, c)), (add_(b, d))));
	let temp_83_1 = (mul_((mul_(d, c)), (add_(d, b))));
	assert(eq_(temp_83_0, temp_83_1)) by {
		cong_mul_(mul_(d, c), add_(b, d), mul_(d, c), add_(d, b));
		lemma_add_comm(b, d);
		lemma_eq_ref(mul_(d, c));
	}
	let temp_84_0 = (mul_((sub_(d, b)), (mul_(a, c))));
	let temp_84_1 = (mul_((mul_(a, c)), (sub_(d, b))));
	assert(eq_(temp_84_0, temp_84_1)) by {
		lemma_mul_comm(sub_(d, b), mul_(a, c));
	}
	let temp_85_0 = (mul_((mul_(d, c)), (mul_(b, c))));
	let temp_85_1 = (mul_((mul_(c, d)), (mul_(b, c))));
	assert(eq_(temp_85_0, temp_85_1)) by {
		cong_mul_(mul_(d, c), mul_(b, c), mul_(c, d), mul_(b, c));
		lemma_mul_comm(d, c);
		lemma_eq_ref(mul_(b, c));
	}
	let temp_86_0 = (sub_((mul_(a, a)), (mul_(a, a))));
	let temp_86_1 = (mul_((sub_(a, a)), a));
	assert(eq_(temp_86_0, temp_86_1)) by {
		lemma_eq_sym(temp_86_1, temp_86_0);
		lemma_mul_dist(a, a, a);
	}
	let temp_87_0 = (mul_((mul_(d, d)), (mod_((sub_(b, c)), m))));
	let temp_87_1 = (mul_((mul_(d, d)), (mod_((sub_(b, c)), m))));
	assert(eq_(temp_87_0, temp_87_1)) by {
		lemma_eq_ref(temp_87_0);
	}
	let temp_88_0 = (mul_((mul_(d, c)), (mod_((mul_(d, a)), m))));
	let temp_88_1 = (mul_((mul_(c, d)), (mod_((mul_(d, a)), m))));
	assert(eq_(temp_88_0, temp_88_1)) by {
		lemma_mul_comm(d, c);
		cong_mul_(mul_(d, c), mod_(mul_(d, a), m), mul_(c, d), mod_(mul_(d, a), m));
		lemma_eq_ref(mod_(mul_(d, a), m));
	}
	let temp_89_0 = (mul_((mod_((add_(b, c)), m)), (add_(a, c))));
	let temp_89_1 = (add_((mul_((mod_((add_(b, c)), m)), a)), (mul_((mod_((add_(b, c)), m)), c))));
	assert(eq_(temp_89_0, temp_89_1)) by {
		lemma_mul_dist(mod_(add_(b, c), m), a, c);
	}
	let temp_90_0 = (mul_((mul_(b, c)), (sub_(d, c))));
	let temp_90_1 = (mul_(b, (mul_(c, (sub_(d, c))))));
	assert(eq_(temp_90_0, temp_90_1)) by {
		lemma_eq_sym(temp_90_1, temp_90_0);
		lemma_mul_assoc(b, c, sub_(d, c));
	}
	let temp_91_0 = (mul_((mul_(a, as_elem(6))), (mod_((mul_(c, b)), m))));
	let temp_91_1 = (mul_(a, (mul_(as_elem(6), (mod_((mul_(c, b)), m))))));
	assert(eq_(temp_91_0, temp_91_1)) by {
		lemma_mul_assoc(a, as_elem(6), mod_(mul_(c, b), m));
		lemma_eq_sym(temp_91_1, temp_91_0);
	}
	let temp_92_0 = (mul_((mul_(b, c)), (mul_((mod_(a, m)), b))));
	let temp_92_1 = (mul_((mul_(c, b)), (mul_((mod_(a, m)), b))));
	assert(eq_(temp_92_0, temp_92_1)) by {
		lemma_mul_comm(b, c);
		cong_mul_(mul_(b, c), mul_(mod_(a, m), b), mul_(c, b), mul_(mod_(a, m), b));
		lemma_eq_ref(mul_(mod_(a, m), b));
	}
	let temp_93_0 = (mul_((mul_(c, c)), d));
	let temp_93_1 = (mul_(c, (mul_(c, d))));
	assert(eq_(temp_93_0, temp_93_1)) by {
		lemma_eq_sym(temp_93_1, temp_93_0);
		lemma_mul_assoc(c, c, d);
	}
	let temp_94_0 = (add_((add_(b, d)), (mul_(d, d))));
	let temp_94_1 = (add_((add_(b, d)), (mul_(d, d))));
	assert(eq_(temp_94_0, temp_94_1)) by {
		lemma_eq_ref(temp_94_0);
	}
	let temp_95_0 = (mul_((mul_(a, d)), (mod_((mul_(c, b)), m))));
	let temp_95_1 = (mul_(a, (mul_(d, (mod_((mul_(c, b)), m))))));
	assert(eq_(temp_95_0, temp_95_1)) by {
		lemma_mul_assoc(a, d, mod_(mul_(c, b), m));
		lemma_eq_sym(temp_95_1, temp_95_0);
	}
	let temp_96_0 = (mul_((mul_(c, (mod_(c, m)))), (mul_(a, d))));
	let temp_96_1 = (mul_((mul_(c, (mod_((add_(c, (mul_((mul_((mul_(a, d)), (mul_(a, b)))), m)))), m)))), (mul_(a, d))));
	assert(eq_(temp_96_0, temp_96_1)) by {
		lemma_mod_mul_vanish(c, mul_(mul_(a, d), mul_(a, b)), m);
		cong_mul_(mul_(c, mod_(c, m)), mul_(a, d), mul_(c, mod_(add_(c, mul_(mul_(mul_(a, d), mul_(a, b)), m)), m)), mul_(a, d));
		lemma_eq_ref(c);
		cong_mul_(c, mod_(c, m), c, mod_(add_(c, mul_(mul_(mul_(a, d), mul_(a, b)), m)), m));
		lemma_eq_ref(mul_(a, d));
	}
	let temp_97_0 = (mul_((mul_(b, d)), (mul_(c, c))));
	let temp_97_1 = (mul_((mul_(c, c)), (mul_(b, d))));
	assert(eq_(temp_97_0, temp_97_1)) by {
		lemma_mul_comm(mul_(b, d), mul_(c, c));
	}
	let temp_98_0 = (mod_((mul_((mul_(d, d)), (mul_(b, c)))), m));
	let temp_98_1 = (mod_((add_((mul_((mul_(d, d)), (mul_(b, c)))), (mul_((mul_((mul_((mod_(b, m)), b)), (mul_(d, c)))), m)))), m));
	assert(eq_(temp_98_0, temp_98_1)) by {
		lemma_mod_mul_vanish(mul_(mul_(d, d), mul_(b, c)), mul_(mul_(mod_(b, m), b), mul_(d, c)), m);
	}
	let temp_99_0 = (mul_((mul_(a, c)), (mul_(c, b))));
	let temp_99_1 = (mul_(a, (mul_(c, (mul_(c, b))))));
	assert(eq_(temp_99_0, temp_99_1)) by {
		lemma_eq_sym(temp_99_1, temp_99_0);
		lemma_mul_assoc(a, c, mul_(c, b));
	}
	let temp_100_0 = (mul_((sub_(a, d)), (mul_(a, a))));
	let temp_100_1 = (mul_((mul_((sub_(a, d)), a)), a));
	assert(eq_(temp_100_0, temp_100_1)) by {
		lemma_mul_assoc(sub_(a, d), a, a);
	}
	let temp_101_0 = (mul_((mod_((mul_(a, as_elem(76))), m)), (sub_(a, b))));
	let temp_101_1 = (mul_((mod_((mul_(as_elem(76), a)), m)), (sub_(a, b))));
	assert(eq_(temp_101_0, temp_101_1)) by {
		lemma_mul_comm(a, as_elem(76));
		cong_mul_(mod_(mul_(a, as_elem(76)), m), sub_(a, b), mod_(mul_(as_elem(76), a), m), sub_(a, b));
		cong_mod_(mul_(a, as_elem(76)), m, mul_(as_elem(76), a), m);
		lemma_eq_ref(sub_(a, b));
		lemma_eq_ref(m);
	}
	let temp_102_0 = (mul_((mul_(b, b)), (sub_(a, b))));
	let temp_102_1 = (mul_((sub_(a, b)), (mul_(b, b))));
	assert(eq_(temp_102_0, temp_102_1)) by {
		lemma_mul_comm(mul_(b, b), sub_(a, b));
	}
	let temp_103_0 = (mul_((add_(a, (mod_(c, m)))), (mod_((mul_(d, a)), m))));
	let temp_103_1 = (mul_((add_(a, (mod_(c, m)))), (mod_((add_((mul_((mul_((mul_((mod_(c, m)), b)), (mul_(d, b)))), m)), (mul_(d, a)))), m))));
	assert(eq_(temp_103_0, temp_103_1)) by {
		lemma_mod_mul_vanish(mul_(d, a), mul_(mul_(mod_(c, m), b), mul_(d, b)), m);
		cong_mul_(add_(a, mod_(c, m)), mod_(mul_(d, a), m), add_(a, mod_(c, m)), mod_(add_(mul_(mul_(mul_(mod_(c, m), b), mul_(d, b)), m), mul_(d, a)), m));
		lemma_eq_ref(add_(a, mod_(c, m)));
	}
	let temp_104_0 = (mul_((mul_(c, d)), (sub_(a, c))));
	let temp_104_1 = (mul_(c, (mul_(d, (sub_(a, c))))));
	assert(eq_(temp_104_0, temp_104_1)) by {
		lemma_eq_sym(temp_104_1, temp_104_0);
		lemma_mul_assoc(c, d, sub_(a, c));
	}
	let temp_105_0 = (mul_((sub_(a, d)), (mul_(c, d))));
	let temp_105_1 = (mul_((mul_((sub_(a, d)), c)), d));
	assert(eq_(temp_105_0, temp_105_1)) by {
		lemma_mul_assoc(sub_(a, d), c, d);
	}
	let temp_106_0 = (mul_((mul_(c, (mod_(as_elem(85), m)))), (mul_(as_elem(41), b))));
	let temp_106_1 = (mul_((mul_(as_elem(41), b)), (mul_(c, (mod_(as_elem(85), m))))));
	assert(eq_(temp_106_0, temp_106_1)) by {
		lemma_mul_comm(mul_(c, mod_(as_elem(85), m)), mul_(as_elem(41), b));
	}
	let temp_107_0 = (mod_((mul_((mul_(b, (mod_(a, m)))), (mod_((mul_(c, d)), m)))), m));
	let temp_107_1 = (mod_((mul_((mul_((mod_(a, m)), b)), (mod_((mul_(c, d)), m)))), m));
	assert(eq_(temp_107_0, temp_107_1)) by {
		lemma_mul_comm(b, mod_(a, m));
		cong_mod_(mul_(mul_(b, mod_(a, m)), mod_(mul_(c, d), m)), m, mul_(mul_(mod_(a, m), b), mod_(mul_(c, d), m)), m);
		lemma_eq_ref(mod_(mul_(c, d), m));
		cong_mul_(mul_(b, mod_(a, m)), mod_(mul_(c, d), m), mul_(mod_(a, m), b), mod_(mul_(c, d), m));
		lemma_eq_ref(m);
	}
	let temp_108_0 = (mul_((mul_(as_elem(3), c)), (mul_(a, c))));
	let temp_108_1 = (mul_((mul_(c, as_elem(3))), (mul_(a, c))));
	assert(eq_(temp_108_0, temp_108_1)) by {
		cong_mul_(mul_(as_elem(3), c), mul_(a, c), mul_(c, as_elem(3)), mul_(a, c));
		lemma_mul_comm(as_elem(3), c);
		lemma_eq_ref(mul_(a, c));
	}
	let temp_109_0 = (mul_((mul_(d, (mod_(c, m)))), (mul_(as_elem(67), c))));
	let temp_109_1 = (mul_((mul_(d, (mod_((add_(c, (mul_((mul_((mod_((add_(b, b)), m)), (mul_(c, d)))), m)))), m)))), (mul_(as_elem(67), c))));
	assert(eq_(temp_109_0, temp_109_1)) by {
		lemma_mod_mul_vanish(c, mul_(mod_(add_(b, b), m), mul_(c, d)), m);
		cong_mul_(mul_(d, mod_(c, m)), mul_(as_elem(67), c), mul_(d, mod_(add_(c, mul_(mul_(mod_(add_(b, b), m), mul_(c, d)), m)), m)), mul_(as_elem(67), c));
		lemma_eq_ref(d);
		cong_mul_(d, mod_(c, m), d, mod_(add_(c, mul_(mul_(mod_(add_(b, b), m), mul_(c, d)), m)), m));
		lemma_eq_ref(mul_(as_elem(67), c));
	}

}

} // verus!