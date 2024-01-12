use builtin_macros::*;
// use builtin::*;
mod nl_basics;
use crate::nl_basics::*;
verus! {

pub proof fn free_0(a: Elem, b: Elem, c: Elem, d: Elem, m: Elem)
{
	let temp_0_0 = (add_((add_(c, c)), (sub_(a, c))));
	let temp_0_1 = (add_((add_(c, c)), (sub_(a, c))));
	assert(eq_(temp_0_0, temp_0_1)) by {
		lemma_eq_ref(temp_0_0);
	}
	let temp_1_0 = (mul_((mul_(c, b)), (add_(d, a))));
	let temp_1_1 = (add_((mul_((mul_(c, b)), d)), (mul_((mul_(c, b)), a))));
	assert(eq_(temp_1_0, temp_1_1)) by {
		lemma_mul_dist(mul_(c, b), d, a);
	}
	let temp_2_0 = (mul_((sub_((mod_(c, m)), a)), (add_(b, a))));
	let temp_2_1 = (mul_((sub_((mod_(c, m)), a)), (add_(a, b))));
	assert(eq_(temp_2_0, temp_2_1)) by {
		lemma_add_comm(b, a);
		cong_mul_(sub_(mod_(c, m), a), add_(b, a), sub_(mod_(c, m), a), add_(a, b));
		lemma_eq_ref(sub_(mod_(c, m), a));
	}
	let temp_3_0 = (mul_((mul_(d, c)), (mod_((mul_(a, a)), m))));
	let temp_3_1 = (mul_((mul_(d, c)), (mod_((add_((mul_(a, a)), (mul_((mul_((mul_(a, a)), (mod_((add_(c, (mod_(c, m)))), m)))), m)))), m))));
	assert(eq_(temp_3_0, temp_3_1)) by {
		lemma_eq_ref(mul_(d, c));
		lemma_mod_mul_vanish(mul_(a, a), mul_(mul_(a, a), mod_(add_(c, mod_(c, m)), m)), m);
		cong_mul_(mul_(d, c), mod_(mul_(a, a), m), mul_(d, c), mod_(add_(mul_(a, a), mul_(mul_(mul_(a, a), mod_(add_(c, mod_(c, m)), m)), m)), m));
	}
	let temp_4_0 = (mul_((mul_(c, a)), (mul_(a, d))));
	let temp_4_1 = (mul_(c, (mul_(a, (mul_(a, d))))));
	assert(eq_(temp_4_0, temp_4_1)) by {
		lemma_eq_sym(temp_4_1, temp_4_0);
		lemma_mul_assoc(c, a, mul_(a, d));
	}
	let temp_5_0 = (add_((mul_(a, a)), (add_(c, b))));
	let temp_5_1 = (add_((mul_(a, a)), (add_(c, b))));
	assert(eq_(temp_5_0, temp_5_1)) by {
		lemma_eq_ref(temp_5_0);
	}
	let temp_6_0 = (mul_((mul_(a, (mod_(d, m)))), (sub_(d, b))));
	let temp_6_1 = (mul_((sub_(d, b)), (mul_(a, (mod_(d, m))))));
	assert(eq_(temp_6_0, temp_6_1)) by {
		lemma_mul_comm(mul_(a, mod_(d, m)), sub_(d, b));
	}
	let temp_7_0 = (mul_((mod_((mul_((mod_(a, m)), d)), m)), (mul_(c, (mod_(c, m))))));
	let temp_7_1 = (mul_((mod_((mul_((mod_((add_(a, (mul_((mul_((mul_((mod_(b, m)), b)), (mul_(d, d)))), m)))), m)), d)), m)), (mul_(c, (mod_(c, m))))));
	assert(eq_(temp_7_0, temp_7_1)) by {
		cong_mul_(mod_(mul_(mod_(a, m), d), m), mul_(c, mod_(c, m)), mod_(mul_(mod_(add_(a, mul_(mul_(mul_(mod_(b, m), b), mul_(d, d)), m)), m), d), m), mul_(c, mod_(c, m)));
		lemma_mod_mul_vanish(a, mul_(mul_(mod_(b, m), b), mul_(d, d)), m);
		lemma_eq_ref(mul_(c, mod_(c, m)));
		cong_mod_(mul_(mod_(a, m), d), m, mul_(mod_(add_(a, mul_(mul_(mul_(mod_(b, m), b), mul_(d, d)), m)), m), d), m);
		lemma_eq_ref(d);
		cong_mul_(mod_(a, m), d, mod_(add_(a, mul_(mul_(mul_(mod_(b, m), b), mul_(d, d)), m)), m), d);
		lemma_eq_ref(m);
	}
	let temp_8_0 = (mul_((mul_(b, b)), (mul_((mod_(d, m)), c))));
	let temp_8_1 = (mul_((mul_(b, b)), (mul_((mod_((sub_(d, (mul_((mul_((mul_(c, c)), (add_(c, d)))), m)))), m)), c))));
	assert(eq_(temp_8_0, temp_8_1)) by {
		cong_mul_(mod_(d, m), c, mod_(sub_(d, mul_(mul_(mul_(c, c), add_(c, d)), m)), m), c);
		lemma_eq_ref(c);
		lemma_mul_comm(b, b);
		lemma_mod_mul_vanish(d, mul_(mul_(c, c), add_(c, d)), m);
		cong_mul_(mul_(b, b), mul_(mod_(d, m), c), mul_(b, b), mul_(mod_(sub_(d, mul_(mul_(mul_(c, c), add_(c, d)), m)), m), c));
	}
	let temp_9_0 = (mul_((mul_(c, (mod_(b, m)))), (mul_(a, (mod_(b, m))))));
	let temp_9_1 = (mul_((mul_(a, (mod_(b, m)))), (mul_(c, (mod_(b, m))))));
	assert(eq_(temp_9_0, temp_9_1)) by {
		lemma_mul_comm(mul_(c, mod_(b, m)), mul_(a, mod_(b, m)));
	}
	let temp_10_0 = (mul_((mul_(d, a)), (sub_(b, b))));
	let temp_10_1 = (mul_(d, (mul_(a, (sub_(b, b))))));
	assert(eq_(temp_10_0, temp_10_1)) by {
		lemma_eq_sym(temp_10_1, temp_10_0);
		lemma_mul_assoc(d, a, sub_(b, b));
	}
	let temp_11_0 = (sub_((mul_(b, c)), (mul_(b, a))));
	let temp_11_1 = (sub_((mul_(c, b)), (mul_(b, a))));
	assert(eq_(temp_11_0, temp_11_1)) by {
		cong_sub_(mul_(b, c), mul_(b, a), mul_(c, b), mul_(b, a));
		lemma_mul_comm(b, c);
		lemma_eq_ref(mul_(b, a));
	}
	let temp_12_0 = (mul_((mul_(c, b)), (mul_(a, d))));
	let temp_12_1 = (mul_((mul_(b, c)), (mul_(a, d))));
	assert(eq_(temp_12_0, temp_12_1)) by {
		lemma_eq_ref(mul_(a, d));
		cong_mul_(mul_(c, b), mul_(a, d), mul_(b, c), mul_(a, d));
		lemma_mul_comm(c, b);
	}
	let temp_13_0 = (mul_((mul_(d, d)), (add_(as_elem(43), (mod_(a, m))))));
	let temp_13_1 = (mul_((mul_(d, d)), (add_(as_elem(43), (mod_((add_((mul_((mul_((add_(a, b)), (mod_((mul_(b, a)), m)))), m)), a)), m))))));
	assert(eq_(temp_13_0, temp_13_1)) by {
		lemma_mul_comm(d, d);
		lemma_mod_mul_vanish(a, mul_(add_(a, b), mod_(mul_(b, a), m)), m);
		cong_mul_(mul_(d, d), add_(as_elem(43), mod_(a, m)), mul_(d, d), add_(as_elem(43), mod_(add_(mul_(mul_(add_(a, b), mod_(mul_(b, a), m)), m), a), m)));
		lemma_eq_ref(as_elem(43));
		cong_add_(as_elem(43), mod_(a, m), as_elem(43), mod_(add_(mul_(mul_(add_(a, b), mod_(mul_(b, a), m)), m), a), m));
	}
	let temp_14_0 = (mul_((mul_(b, d)), (mul_(c, d))));
	let temp_14_1 = (mul_((mul_(b, d)), (mul_(d, c))));
	assert(eq_(temp_14_0, temp_14_1)) by {
		cong_mul_(mul_(b, d), mul_(c, d), mul_(b, d), mul_(d, c));
		lemma_mul_comm(c, d);
		lemma_eq_ref(mul_(b, d));
	}
	let temp_15_0 = (mul_((mul_(a, d)), (add_(a, b))));
	let temp_15_1 = (mul_((mul_(d, a)), (add_(a, b))));
	assert(eq_(temp_15_0, temp_15_1)) by {
		cong_mul_(mul_(a, d), add_(a, b), mul_(d, a), add_(a, b));
		lemma_mul_comm(a, d);
		lemma_eq_ref(add_(a, b));
	}
	let temp_16_0 = (mul_((mul_(d, b)), (mul_(c, d))));
	let temp_16_1 = (mul_(d, (mul_(b, (mul_(c, d))))));
	assert(eq_(temp_16_0, temp_16_1)) by {
		lemma_eq_sym(temp_16_1, temp_16_0);
		lemma_mul_assoc(d, b, mul_(c, d));
	}
	let temp_17_0 = (mul_((mul_(b, (mod_(d, m)))), (sub_(c, d))));
	let temp_17_1 = (mul_((sub_(c, d)), (mul_(b, (mod_(d, m))))));
	assert(eq_(temp_17_0, temp_17_1)) by {
		lemma_mul_comm(mul_(b, mod_(d, m)), sub_(c, d));
	}
	let temp_18_0 = (mul_((mul_(c, b)), (sub_(c, a))));
	let temp_18_1 = (mul_((mul_(b, c)), (sub_(c, a))));
	assert(eq_(temp_18_0, temp_18_1)) by {
		cong_mul_(mul_(c, b), sub_(c, a), mul_(b, c), sub_(c, a));
		lemma_mul_comm(c, b);
		lemma_eq_ref(sub_(c, a));
	}
	let temp_19_0 = (mul_((mod_((mul_((mod_(b, m)), b)), m)), (mul_(b, c))));
	let temp_19_1 = (mul_((mod_((add_((mul_((mod_(b, m)), b)), (mul_((mul_((mul_(d, c)), (mul_(b, d)))), m)))), m)), (mul_(b, c))));
	assert(eq_(temp_19_0, temp_19_1)) by {
		lemma_mod_mul_vanish(mul_(mod_(b, m), b), mul_(mul_(d, c), mul_(b, d)), m);
		cong_mul_(mod_(mul_(mod_(b, m), b), m), mul_(b, c), mod_(add_(mul_(mod_(b, m), b), mul_(mul_(mul_(d, c), mul_(b, d)), m)), m), mul_(b, c));
		lemma_eq_ref(mul_(b, c));
	}
	let temp_20_0 = (mul_((mul_(c, c)), (mul_(b, a))));
	let temp_20_1 = (mul_(c, (mul_(c, (mul_(b, a))))));
	assert(eq_(temp_20_0, temp_20_1)) by {
		lemma_eq_sym(temp_20_1, temp_20_0);
		lemma_mul_assoc(c, c, mul_(b, a));
	}
	let temp_21_0 = (sub_((mul_(b, d)), (mod_((mul_(a, a)), m))));
	let temp_21_1 = (sub_((mul_(d, b)), (mod_((mul_(a, a)), m))));
	assert(eq_(temp_21_0, temp_21_1)) by {
		lemma_mul_comm(b, d);
		cong_sub_(mul_(b, d), mod_(mul_(a, a), m), mul_(d, b), mod_(mul_(a, a), m));
		lemma_eq_ref(mod_(mul_(a, a), m));
	}
	let temp_22_0 = (mul_((mul_(c, a)), (mul_(b, d))));
	let temp_22_1 = (mul_((mul_((mul_(c, a)), b)), d));
	assert(eq_(temp_22_0, temp_22_1)) by {
		lemma_mul_assoc(mul_(c, a), b, d);
	}
	let temp_23_0 = (mod_((mul_((mul_(d, (mod_(d, m)))), (mul_(b, (mod_(d, m)))))), m));
	let temp_23_1 = (mod_((mul_((mul_(d, (mod_((add_((mul_((mul_((sub_(d, c)), (mul_(d, as_elem(42))))), m)), d)), m)))), (mul_(b, (mod_(d, m)))))), m));
	assert(eq_(temp_23_0, temp_23_1)) by {
		lemma_mod_mul_vanish(d, mul_(sub_(d, c), mul_(d, as_elem(42))), m);
		cong_mod_(mul_(mul_(d, mod_(d, m)), mul_(b, mod_(d, m))), m, mul_(mul_(d, mod_(add_(mul_(mul_(sub_(d, c), mul_(d, as_elem(42))), m), d), m)), mul_(b, mod_(d, m))), m);
		cong_mul_(mul_(d, mod_(d, m)), mul_(b, mod_(d, m)), mul_(d, mod_(add_(mul_(mul_(sub_(d, c), mul_(d, as_elem(42))), m), d), m)), mul_(b, mod_(d, m)));
		lemma_eq_ref(mul_(b, mod_(d, m)));
		lemma_eq_ref(d);
		cong_mul_(d, mod_(d, m), d, mod_(add_(mul_(mul_(sub_(d, c), mul_(d, as_elem(42))), m), d), m));
		lemma_eq_ref(m);
	}
	let temp_24_0 = (mul_((mul_(c, c)), d));
	let temp_24_1 = (mul_(c, (mul_(c, d))));
	assert(eq_(temp_24_0, temp_24_1)) by {
		lemma_eq_sym(temp_24_1, temp_24_0);
		lemma_mul_assoc(c, c, d);
	}
	let temp_25_0 = (mod_((mul_((mul_(d, c)), a)), m));
	let temp_25_1 = (mod_((mul_(d, (mul_(c, a)))), m));
	assert(eq_(temp_25_0, temp_25_1)) by {
		lemma_mul_assoc(d, c, a);
		cong_mod_(mul_(mul_(d, c), a), m, mul_(d, mul_(c, a)), m);
		lemma_eq_sym(mul_(d, mul_(c, a)), mul_(mul_(d, c), a));
		lemma_eq_ref(m);
	}
	let temp_26_0 = (mul_((mul_(a, (mod_(d, m)))), (mod_((mul_(b, d)), m))));
	let temp_26_1 = (mul_((mul_((mod_(d, m)), a)), (mod_((mul_(b, d)), m))));
	assert(eq_(temp_26_0, temp_26_1)) by {
		lemma_mul_comm(a, mod_(d, m));
		cong_mul_(mul_(a, mod_(d, m)), mod_(mul_(b, d), m), mul_(mod_(d, m), a), mod_(mul_(b, d), m));
		lemma_eq_ref(mod_(mul_(b, d), m));
	}
	let temp_27_0 = (mul_((mul_(b, b)), (add_(a, a))));
	let temp_27_1 = (mul_(b, (mul_(b, (add_(a, a))))));
	assert(eq_(temp_27_0, temp_27_1)) by {
		lemma_eq_sym(temp_27_1, temp_27_0);
		lemma_mul_assoc(b, b, add_(a, a));
	}
	let temp_28_0 = (add_((mul_(a, d)), (mul_(b, c))));
	let temp_28_1 = (add_((mul_(b, c)), (mul_(a, d))));
	assert(eq_(temp_28_0, temp_28_1)) by {
		lemma_add_comm(mul_(a, d), mul_(b, c));
	}
	let temp_29_0 = (mul_((mul_(c, b)), (add_(a, d))));
	let temp_29_1 = (mul_((add_(a, d)), (mul_(c, b))));
	assert(eq_(temp_29_0, temp_29_1)) by {
		lemma_mul_comm(mul_(c, b), add_(a, d));
	}
	let temp_30_0 = (add_((mod_((mul_(d, b)), m)), (mul_(c, d))));
	let temp_30_1 = (add_((mod_((add_((mul_((mul_((sub_(c, d)), (mul_(b, a)))), m)), (mul_(d, b)))), m)), (mul_(c, d))));
	assert(eq_(temp_30_0, temp_30_1)) by {
		lemma_mod_mul_vanish(mul_(d, b), mul_(sub_(c, d), mul_(b, a)), m);
		cong_add_(mod_(mul_(d, b), m), mul_(c, d), mod_(add_(mul_(mul_(sub_(c, d), mul_(b, a)), m), mul_(d, b)), m), mul_(c, d));
		lemma_eq_ref(mul_(c, d));
	}
	let temp_31_0 = (mul_((sub_(a, d)), (mul_(b, b))));
	let temp_31_1 = (sub_((mul_(a, (mul_(b, b)))), (mul_(d, (mul_(b, b))))));
	assert(eq_(temp_31_0, temp_31_1)) by {
		lemma_mul_dist(mul_(b, b), a, d);
	}
	let temp_32_0 = (mul_((mul_(a, b)), (mul_(b, a))));
	let temp_32_1 = (mul_((mul_(b, a)), (mul_(a, b))));
	assert(eq_(temp_32_0, temp_32_1)) by {
		lemma_mul_comm(mul_(a, b), mul_(b, a));
	}
	let temp_33_0 = (sub_((mul_(c, b)), (mul_(b, c))));
	let temp_33_1 = (sub_((mul_(b, c)), (mul_(b, c))));
	assert(eq_(temp_33_0, temp_33_1)) by {
		cong_sub_(mul_(c, b), mul_(b, c), mul_(b, c), mul_(b, c));
		lemma_mul_comm(c, b);
		lemma_eq_ref(mul_(b, c));
	}
	let temp_34_0 = (mul_((mul_(b, a)), (mod_((mul_(b, c)), m))));
	let temp_34_1 = (mul_((mul_(b, a)), (mod_((mul_(c, b)), m))));
	assert(eq_(temp_34_0, temp_34_1)) by {
		lemma_eq_ref(mul_(b, a));
		lemma_mul_comm(c, b);
		cong_mul_(mul_(b, a), mod_(mul_(b, c), m), mul_(b, a), mod_(mul_(c, b), m));
		lemma_eq_sym(mod_(mul_(c, b), m), mod_(mul_(b, c), m));
		cong_mod_(mul_(c, b), m, mul_(b, c), m);
		lemma_eq_ref(m);
	}
	let temp_35_0 = (mul_((sub_(a, c)), (mul_(b, b))));
	let temp_35_1 = (mul_((mul_((sub_(a, c)), b)), b));
	assert(eq_(temp_35_0, temp_35_1)) by {
		lemma_mul_assoc(sub_(a, c), b, b);
	}
	let temp_36_0 = (mul_((mul_(a, a)), (mul_(d, a))));
	let temp_36_1 = (mul_((mul_(a, a)), (mul_(d, a))));
	assert(eq_(temp_36_0, temp_36_1)) by {
		lemma_eq_ref(temp_36_0);
	}
	let temp_37_0 = (mul_((mul_(a, d)), (mul_(d, (mod_(b, m))))));
	let temp_37_1 = (mul_((mul_(a, d)), (mul_((mod_(b, m)), d))));
	assert(eq_(temp_37_0, temp_37_1)) by {
		lemma_eq_ref(mul_(a, d));
		lemma_mul_comm(d, mod_(b, m));
		cong_mul_(mul_(a, d), mul_(d, mod_(b, m)), mul_(a, d), mul_(mod_(b, m), d));
	}
	let temp_38_0 = (mul_((mul_(a, c)), (mul_(c, d))));
	let temp_38_1 = (mul_((mul_(c, a)), (mul_(c, d))));
	assert(eq_(temp_38_0, temp_38_1)) by {
		cong_mul_(mul_(a, c), mul_(c, d), mul_(c, a), mul_(c, d));
		lemma_mul_comm(a, c);
		lemma_eq_ref(mul_(c, d));
	}
	let temp_39_0 = (mul_((mod_((add_(b, (mod_(a, m)))), m)), (mul_(d, a))));
	let temp_39_1 = (mul_((mod_((add_((mod_(b, m)), (mod_(a, m)))), m)), (mul_(d, a))));
	assert(eq_(temp_39_0, temp_39_1)) by {
		lemma_mod_add_noop(b, mod_(a, m), m);
		cong_mul_(mod_(add_(b, mod_(a, m)), m), mul_(d, a), mod_(add_(mod_(b, m), mod_(a, m)), m), mul_(d, a));
		lemma_eq_ref(mul_(d, a));
	}
	let temp_40_0 = (add_((add_(a, d)), (mul_(a, d))));
	let temp_40_1 = (add_((add_(a, d)), (mul_(d, a))));
	assert(eq_(temp_40_0, temp_40_1)) by {
		cong_add_(add_(a, d), mul_(a, d), add_(a, d), mul_(d, a));
		lemma_mul_comm(a, d);
		lemma_eq_ref(add_(a, d));
	}
	let temp_41_0 = (mul_((mul_(a, (mod_(d, m)))), (mul_(c, (mod_(c, m))))));
	let temp_41_1 = (mul_((mul_(a, (mod_((sub_(d, (mul_((mul_((mul_(b, a)), (mul_(d, c)))), m)))), m)))), (mul_(c, (mod_(c, m))))));
	assert(eq_(temp_41_0, temp_41_1)) by {
		lemma_mod_mul_vanish(d, mul_(mul_(b, a), mul_(d, c)), m);
		cong_mul_(mul_(a, mod_(d, m)), mul_(c, mod_(c, m)), mul_(a, mod_(sub_(d, mul_(mul_(mul_(b, a), mul_(d, c)), m)), m)), mul_(c, mod_(c, m)));
		lemma_eq_ref(a);
		cong_mul_(a, mod_(d, m), a, mod_(sub_(d, mul_(mul_(mul_(b, a), mul_(d, c)), m)), m));
		lemma_eq_ref(mul_(c, mod_(c, m)));
	}
	let temp_42_0 = (mul_((add_(a, a)), (mul_(b, as_elem(69)))));
	let temp_42_1 = (mul_((add_(a, a)), (mul_(as_elem(69), b))));
	assert(eq_(temp_42_0, temp_42_1)) by {
		cong_mul_(add_(a, a), mul_(b, as_elem(69)), add_(a, a), mul_(as_elem(69), b));
		lemma_mul_comm(b, as_elem(69));
		lemma_eq_ref(add_(a, a));
	}
	let temp_43_0 = (add_((mul_(b, (mod_(as_elem(6), m)))), (mul_(c, d))));
	let temp_43_1 = (add_((mul_(b, (mod_((add_((mul_((mul_((mod_((mul_(c, c)), m)), (mul_(b, a)))), m)), as_elem(6))), m)))), (mul_(c, d))));
	assert(eq_(temp_43_0, temp_43_1)) by {
		cong_add_(mul_(b, mod_(as_elem(6), m)), mul_(c, d), mul_(b, mod_(add_(mul_(mul_(mod_(mul_(c, c), m), mul_(b, a)), m), as_elem(6)), m)), mul_(c, d));
		lemma_mod_mul_vanish(as_elem(6), mul_(mod_(mul_(c, c), m), mul_(b, a)), m);
		lemma_eq_ref(mul_(c, d));
		cong_mul_(b, mod_(as_elem(6), m), b, mod_(add_(mul_(mul_(mod_(mul_(c, c), m), mul_(b, a)), m), as_elem(6)), m));
		lemma_eq_ref(b);
	}
	let temp_44_0 = (mod_((sub_((mod_((sub_(c, c)), m)), (add_(b, d)))), m));
	let temp_44_1 = (mod_((sub_((mod_((sub_(c, c)), m)), (mod_((add_(b, d)), m)))), m));
	assert(eq_(temp_44_0, temp_44_1)) by {
		lemma_mod_sub_noop(mod_(sub_(c, c), m), add_(b, d), m);
	}
	let temp_45_0 = (mul_((add_(c, c)), (mul_(b, a))));
	let temp_45_1 = (mul_((add_(c, c)), (mul_(b, a))));
	assert(eq_(temp_45_0, temp_45_1)) by {
		lemma_eq_ref(temp_45_0);
	}
	let temp_46_0 = (mul_((mul_(d, c)), (mod_((mul_(d, b)), m))));
	let temp_46_1 = (mul_(d, (mul_(c, (mod_((mul_(d, b)), m))))));
	assert(eq_(temp_46_0, temp_46_1)) by {
		lemma_mul_assoc(d, c, mod_(mul_(d, b), m));
		lemma_eq_sym(temp_46_1, temp_46_0);
	}
	let temp_47_0 = (sub_((mul_(b, a)), (mul_(c, c))));
	let temp_47_1 = (sub_((mul_(b, a)), (mul_(c, c))));
	assert(eq_(temp_47_0, temp_47_1)) by {
		lemma_eq_ref(temp_47_0);
	}
	let temp_48_0 = (mul_((mul_(c, c)), (sub_(d, d))));
	let temp_48_1 = (mul_(c, (mul_(c, (sub_(d, d))))));
	assert(eq_(temp_48_0, temp_48_1)) by {
		lemma_eq_sym(temp_48_1, temp_48_0);
		lemma_mul_assoc(c, c, sub_(d, d));
	}
	let temp_49_0 = (mul_(d, (mul_((mod_(c, m)), (mod_(a, m))))));
	let temp_49_1 = (mul_(d, (mul_((mod_((add_((mul_((mod_((mul_((mul_(a, d)), (mul_(c, c)))), m)), m)), c)), m)), (mod_(a, m))))));
	assert(eq_(temp_49_0, temp_49_1)) by {
		lemma_mod_mul_vanish(c, mod_(mul_(mul_(a, d), mul_(c, c)), m), m);
		cong_mul_(d, mul_(mod_(c, m), mod_(a, m)), d, mul_(mod_(add_(mul_(mod_(mul_(mul_(a, d), mul_(c, c)), m), m), c), m), mod_(a, m)));
		lemma_eq_ref(d);
		cong_mul_(mod_(c, m), mod_(a, m), mod_(add_(mul_(mod_(mul_(mul_(a, d), mul_(c, c)), m), m), c), m), mod_(a, m));
		lemma_eq_ref(mod_(a, m));
	}
	let temp_50_0 = (add_((mul_((mod_(a, m)), (mod_(as_elem(95), m)))), (mod_((mul_(d, b)), m))));
	let temp_50_1 = (add_((mod_((mul_(d, b)), m)), (mul_((mod_(a, m)), (mod_(as_elem(95), m))))));
	assert(eq_(temp_50_0, temp_50_1)) by {
		lemma_add_comm(mul_(mod_(a, m), mod_(as_elem(95), m)), mod_(mul_(d, b), m));
	}
	let temp_51_0 = (mul_((add_(a, c)), (sub_(a, d))));
	let temp_51_1 = (add_((mul_(a, (sub_(a, d)))), (mul_(c, (sub_(a, d))))));
	assert(eq_(temp_51_0, temp_51_1)) by {
		lemma_mul_dist(a, c, sub_(a, d));
	}
	let temp_52_0 = (mul_((mul_(c, a)), (mod_((sub_(a, d)), m))));
	let temp_52_1 = (mul_(c, (mul_(a, (mod_((sub_(a, d)), m))))));
	assert(eq_(temp_52_0, temp_52_1)) by {
		lemma_mul_assoc(c, a, mod_(sub_(a, d), m));
		lemma_eq_sym(temp_52_1, temp_52_0);
	}
	let temp_53_0 = (mod_((add_((mul_(d, c)), (sub_((mod_(b, m)), a)))), m));
	let temp_53_1 = (mod_((add_((mul_(d, c)), (sub_((mod_((add_(b, (mul_((mul_(d, (sub_(c, a)))), m)))), m)), a)))), m));
	assert(eq_(temp_53_0, temp_53_1)) by {
		lemma_mod_mul_vanish(b, mul_(d, sub_(c, a)), m);
		cong_mod_(add_(mul_(d, c), sub_(mod_(b, m), a)), m, add_(mul_(d, c), sub_(mod_(add_(b, mul_(mul_(d, sub_(c, a)), m)), m), a)), m);
		cong_add_(mul_(d, c), sub_(mod_(b, m), a), mul_(d, c), sub_(mod_(add_(b, mul_(mul_(d, sub_(c, a)), m)), m), a));
		lemma_eq_ref(m);
		lemma_eq_ref(mul_(d, c));
		lemma_eq_ref(a);
		cong_sub_(mod_(b, m), a, mod_(add_(b, mul_(mul_(d, sub_(c, a)), m)), m), a);
	}
	let temp_54_0 = (mul_((mul_(d, (mod_(a, m)))), (sub_(d, a))));
	let temp_54_1 = (mul_(d, (mul_((mod_(a, m)), (sub_(d, a))))));
	assert(eq_(temp_54_0, temp_54_1)) by {
		lemma_eq_sym(temp_54_1, temp_54_0);
		lemma_mul_assoc(d, mod_(a, m), sub_(d, a));
	}
	let temp_55_0 = (mod_((sub_((mul_(d, as_elem(44))), (mul_(d, d)))), m));
	let temp_55_1 = (mod_((sub_((mul_(d, as_elem(44))), (mul_(d, d)))), m));
	assert(eq_(temp_55_0, temp_55_1)) by {
		lemma_eq_ref(temp_55_0);
	}
	let temp_56_0 = (mul_((mul_(b, b)), (sub_(a, a))));
	let temp_56_1 = (mul_((mul_(b, b)), (sub_(a, a))));
	assert(eq_(temp_56_0, temp_56_1)) by {
		lemma_eq_ref(temp_56_0);
	}
	let temp_57_0 = (sub_((mul_(a, b)), (mul_(a, d))));
	let temp_57_1 = (sub_((mul_(b, a)), (mul_(a, d))));
	assert(eq_(temp_57_0, temp_57_1)) by {
		cong_sub_(mul_(a, b), mul_(a, d), mul_(b, a), mul_(a, d));
		lemma_mul_comm(a, b);
		lemma_eq_ref(mul_(a, d));
	}
	let temp_58_0 = (mod_((sub_((mul_(d, b)), (mul_(c, d)))), m));
	let temp_58_1 = (mod_((sub_((mod_((mul_(d, b)), m)), (mul_(c, d)))), m));
	assert(eq_(temp_58_0, temp_58_1)) by {
		lemma_mod_sub_noop(mul_(d, b), mul_(c, d), m);
	}
	let temp_59_0 = (add_((sub_((mod_(a, m)), d)), (mod_((mul_(d, d)), m))));
	let temp_59_1 = (add_((sub_((mod_(a, m)), d)), (mod_((sub_((mul_(d, d)), (mul_((mul_((mul_(a, a)), (mul_(d, b)))), m)))), m))));
	assert(eq_(temp_59_0, temp_59_1)) by {
		lemma_mod_mul_vanish(mul_(d, d), mul_(mul_(a, a), mul_(d, b)), m);
		cong_add_(sub_(mod_(a, m), d), mod_(mul_(d, d), m), sub_(mod_(a, m), d), mod_(sub_(mul_(d, d), mul_(mul_(mul_(a, a), mul_(d, b)), m)), m));
		lemma_eq_ref(sub_(mod_(a, m), d));
	}
	let temp_60_0 = (mul_((mul_(b, (mod_(d, m)))), (mul_(c, d))));
	let temp_60_1 = (mul_((mul_(b, (mod_((add_(d, (mul_((sub_((mul_(a, a)), (mul_(d, d)))), m)))), m)))), (mul_(c, d))));
	assert(eq_(temp_60_0, temp_60_1)) by {
		lemma_mod_mul_vanish(d, sub_(mul_(a, a), mul_(d, d)), m);
		cong_mul_(mul_(b, mod_(d, m)), mul_(c, d), mul_(b, mod_(add_(d, mul_(sub_(mul_(a, a), mul_(d, d)), m)), m)), mul_(c, d));
		lemma_eq_ref(b);
		cong_mul_(b, mod_(d, m), b, mod_(add_(d, mul_(sub_(mul_(a, a), mul_(d, d)), m)), m));
		lemma_eq_ref(mul_(c, d));
	}
	let temp_61_0 = (mul_((sub_(a, a)), (mod_((mul_(b, (mod_(a, m)))), m))));
	let temp_61_1 = (mul_((sub_(a, a)), (mod_((mod_((mul_(a, b)), m)), m))));
	assert(eq_(temp_61_0, temp_61_1)) by {
		lemma_mod_mul_noop(a, b, m);
		cong_mul_(sub_(a, a), mod_(mul_(b, mod_(a, m)), m), sub_(a, a), mod_(mod_(mul_(a, b), m), m));
		lemma_eq_sym(mod_(mod_(mul_(a, b), m), m), mod_(mul_(b, mod_(a, m)), m));
		lemma_eq_ref(sub_(a, a));
	}
	let temp_62_0 = (mul_((mul_(b, c)), (mul_(b, a))));
	let temp_62_1 = (mul_((mul_((mul_(b, c)), b)), a));
	assert(eq_(temp_62_0, temp_62_1)) by {
		lemma_mul_assoc(mul_(b, c), b, a);
	}
	let temp_63_0 = (mul_((mul_(d, a)), (mul_(b, b))));
	let temp_63_1 = (mul_((mul_(d, a)), (mul_(b, b))));
	assert(eq_(temp_63_0, temp_63_1)) by {
		lemma_eq_ref(temp_63_0);
	}
	let temp_64_0 = (mod_((sub_((mul_(d, a)), (mul_(b, c)))), m));
	let temp_64_1 = (mod_((sub_((mod_((mul_(d, a)), m)), (mod_((mul_(b, c)), m)))), m));
	assert(eq_(temp_64_0, temp_64_1)) by {
		lemma_mod_sub_noop(mul_(d, a), mul_(b, c), m);
	}
	let temp_65_0 = (mul_((mul_(a, d)), (mul_((mod_(c, m)), b))));
	let temp_65_1 = (mul_((mul_((mod_(c, m)), b)), (mul_(a, d))));
	assert(eq_(temp_65_0, temp_65_1)) by {
		lemma_mul_comm(mul_(a, d), mul_(mod_(c, m), b));
	}
	let temp_66_0 = (mul_((mul_(d, b)), (mod_((mul_((mod_(a, m)), d)), m))));
	let temp_66_1 = (mul_(d, (mul_(b, (mod_((mul_((mod_(a, m)), d)), m))))));
	assert(eq_(temp_66_0, temp_66_1)) by {
		lemma_mul_assoc(d, b, mod_(mul_(mod_(a, m), d), m));
		lemma_eq_sym(temp_66_1, temp_66_0);
	}
	let temp_67_0 = (mul_((mod_((mul_(b, d)), m)), (mul_(b, c))));
	let temp_67_1 = (mul_((mul_((mod_((mul_(b, d)), m)), b)), c));
	assert(eq_(temp_67_0, temp_67_1)) by {
		lemma_mul_assoc(mod_(mul_(b, d), m), b, c);
	}
	let temp_68_0 = (sub_((sub_(c, d)), (mul_(d, d))));
	let temp_68_1 = (sub_((sub_(c, d)), (mul_(d, d))));
	assert(eq_(temp_68_0, temp_68_1)) by {
		lemma_eq_ref(temp_68_0);
	}
	let temp_69_0 = (mul_((mul_(a, c)), (mul_(a, c))));
	let temp_69_1 = (mul_(a, (mul_(c, (mul_(a, c))))));
	assert(eq_(temp_69_0, temp_69_1)) by {
		lemma_eq_sym(temp_69_1, temp_69_0);
		lemma_mul_assoc(a, c, mul_(a, c));
	}
	let temp_70_0 = (mul_((mul_(d, d)), (add_(a, b))));
	let temp_70_1 = (mul_((mul_(d, d)), (add_(b, a))));
	assert(eq_(temp_70_0, temp_70_1)) by {
		cong_mul_(mul_(d, d), add_(a, b), mul_(d, d), add_(b, a));
		lemma_add_comm(a, b);
		lemma_mul_comm(d, d);
	}
	let temp_71_0 = (mul_((mul_(as_elem(67), d)), (sub_(a, c))));
	let temp_71_1 = (mul_(as_elem(67), (mul_(d, (sub_(a, c))))));
	assert(eq_(temp_71_0, temp_71_1)) by {
		lemma_mul_assoc(as_elem(67), d, sub_(a, c));
		lemma_eq_sym(temp_71_1, temp_71_0);
	}
	let temp_72_0 = (add_((add_(d, d)), (add_(b, b))));
	let temp_72_1 = (add_((add_(d, d)), (add_(b, b))));
	assert(eq_(temp_72_0, temp_72_1)) by {
		lemma_eq_ref(temp_72_0);
	}
	let temp_73_0 = (mul_((mul_(a, c)), (sub_(c, b))));
	let temp_73_1 = (mul_((sub_(c, b)), (mul_(a, c))));
	assert(eq_(temp_73_0, temp_73_1)) by {
		lemma_mul_comm(mul_(a, c), sub_(c, b));
	}
	let temp_74_0 = (mul_((mod_((mul_(b, a)), m)), (add_(b, b))));
	let temp_74_1 = (mul_((mod_((add_((mul_((mul_((mul_(d, d)), (mul_(b, c)))), m)), (mul_(b, a)))), m)), (add_(b, b))));
	assert(eq_(temp_74_0, temp_74_1)) by {
		lemma_mod_mul_vanish(mul_(b, a), mul_(mul_(d, d), mul_(b, c)), m);
		lemma_add_comm(b, b);
		cong_mul_(mod_(mul_(b, a), m), add_(b, b), mod_(add_(mul_(mul_(mul_(d, d), mul_(b, c)), m), mul_(b, a)), m), add_(b, b));
	}
	let temp_75_0 = (mul_((mul_(d, c)), (mul_(c, b))));
	let temp_75_1 = (mul_((mul_((mul_(d, c)), c)), b));
	assert(eq_(temp_75_0, temp_75_1)) by {
		lemma_mul_assoc(mul_(d, c), c, b);
	}
	let temp_76_0 = (mul_((mul_(a, d)), (mul_(b, a))));
	let temp_76_1 = (mul_((mul_((mul_(a, d)), b)), a));
	assert(eq_(temp_76_0, temp_76_1)) by {
		lemma_mul_assoc(mul_(a, d), b, a);
	}
	let temp_77_0 = (mul_((mul_(c, a)), (mul_(d, d))));
	let temp_77_1 = (mul_(c, (mul_(a, (mul_(d, d))))));
	assert(eq_(temp_77_0, temp_77_1)) by {
		lemma_eq_sym(temp_77_1, temp_77_0);
		lemma_mul_assoc(c, a, mul_(d, d));
	}
	let temp_78_0 = (add_((mul_(c, c)), (sub_(c, d))));
	let temp_78_1 = (add_((mul_(c, c)), (sub_(c, d))));
	assert(eq_(temp_78_0, temp_78_1)) by {
		lemma_eq_ref(temp_78_0);
	}
	let temp_79_0 = (mul_((mul_(b, c)), (mul_(d, b))));
	let temp_79_1 = (mul_((mul_(b, c)), (mul_(b, d))));
	assert(eq_(temp_79_0, temp_79_1)) by {
		cong_mul_(mul_(b, c), mul_(d, b), mul_(b, c), mul_(b, d));
		lemma_mul_comm(d, b);
		lemma_eq_ref(mul_(b, c));
	}
	let temp_80_0 = (mod_((mul_((mod_((mul_(a, c)), m)), (mul_(b, c)))), m));
	let temp_80_1 = (mod_((mul_((mul_((mod_((mul_(a, c)), m)), b)), c)), m));
	assert(eq_(temp_80_0, temp_80_1)) by {
		lemma_mul_assoc(mod_(mul_(a, c), m), b, c);
		cong_mod_(mul_(mod_(mul_(a, c), m), mul_(b, c)), m, mul_(mul_(mod_(mul_(a, c), m), b), c), m);
		lemma_eq_ref(m);
	}
	let temp_81_0 = (mul_((mul_(a, c)), (mod_((mul_(d, b)), m))));
	let temp_81_1 = (mul_((mul_(a, c)), (mod_((add_((mul_((mul_((mul_(b, b)), (mul_(c, d)))), m)), (mul_(d, b)))), m))));
	assert(eq_(temp_81_0, temp_81_1)) by {
		lemma_mod_mul_vanish(mul_(d, b), mul_(mul_(b, b), mul_(c, d)), m);
		cong_mul_(mul_(a, c), mod_(mul_(d, b), m), mul_(a, c), mod_(add_(mul_(mul_(mul_(b, b), mul_(c, d)), m), mul_(d, b)), m));
		lemma_eq_ref(mul_(a, c));
	}
	let temp_82_0 = (mul_((mul_(d, c)), (mul_(a, d))));
	let temp_82_1 = (mul_((mul_(d, c)), (mul_(d, a))));
	assert(eq_(temp_82_0, temp_82_1)) by {
		cong_mul_(mul_(d, c), mul_(a, d), mul_(d, c), mul_(d, a));
		lemma_mul_comm(a, d);
		lemma_eq_ref(mul_(d, c));
	}
	let temp_83_0 = (mul_((sub_((mod_(c, m)), b)), (mul_(d, c))));
	let temp_83_1 = (mul_((sub_((mod_((sub_(c, (mul_((mul_((mod_((mul_(d, (mod_(a, m)))), m)), (sub_(a, b)))), m)))), m)), b)), (mul_(d, c))));
	assert(eq_(temp_83_0, temp_83_1)) by {
		cong_mul_(sub_(mod_(c, m), b), mul_(d, c), sub_(mod_(sub_(c, mul_(mul_(mod_(mul_(d, mod_(a, m)), m), sub_(a, b)), m)), m), b), mul_(d, c));
		lemma_mod_mul_vanish(c, mul_(mod_(mul_(d, mod_(a, m)), m), sub_(a, b)), m);
		cong_sub_(mod_(c, m), b, mod_(sub_(c, mul_(mul_(mod_(mul_(d, mod_(a, m)), m), sub_(a, b)), m)), m), b);
		lemma_eq_ref(mul_(d, c));
		lemma_eq_ref(b);
	}
	let temp_84_0 = (mul_((mul_(c, d)), (mul_(c, b))));
	let temp_84_1 = (mul_((mul_(c, b)), (mul_(c, d))));
	assert(eq_(temp_84_0, temp_84_1)) by {
		lemma_mul_comm(mul_(c, d), mul_(c, b));
	}
	let temp_85_0 = (mul_(a, (mul_(c, a))));
	let temp_85_1 = (mul_(a, (mul_(a, c))));
	assert(eq_(temp_85_0, temp_85_1)) by {
		cong_mul_(a, mul_(c, a), a, mul_(a, c));
		lemma_mul_comm(c, a);
		lemma_eq_ref(a);
	}
	let temp_86_0 = (mul_((sub_(c, as_elem(85))), (mod_((sub_(a, a)), m))));
	let temp_86_1 = (mul_((sub_(c, as_elem(85))), (mod_((add_((mul_((mod_((mul_((mul_(b, a)), (add_(a, d)))), m)), m)), (sub_(a, a)))), m))));
	assert(eq_(temp_86_0, temp_86_1)) by {
		lemma_mod_mul_vanish(sub_(a, a), mod_(mul_(mul_(b, a), add_(a, d)), m), m);
		cong_mul_(sub_(c, as_elem(85)), mod_(sub_(a, a), m), sub_(c, as_elem(85)), mod_(add_(mul_(mod_(mul_(mul_(b, a), add_(a, d)), m), m), sub_(a, a)), m));
		lemma_eq_ref(sub_(c, as_elem(85)));
	}
	let temp_87_0 = (mul_((mul_(a, d)), (mul_(b, c))));
	let temp_87_1 = (mul_(a, (mul_(d, (mul_(b, c))))));
	assert(eq_(temp_87_0, temp_87_1)) by {
		lemma_eq_sym(temp_87_1, temp_87_0);
		lemma_mul_assoc(a, d, mul_(b, c));
	}
	let temp_88_0 = (mul_((mod_((mul_((mod_(b, m)), b)), m)), (add_(d, (mod_(b, m))))));
	let temp_88_1 = (mul_((add_(d, (mod_(b, m)))), (mod_((mul_((mod_(b, m)), b)), m))));
	assert(eq_(temp_88_0, temp_88_1)) by {
		lemma_mul_comm(mod_(mul_(mod_(b, m), b), m), add_(d, mod_(b, m)));
	}
	let temp_89_0 = (mul_((mul_(d, d)), (mul_(d, d))));
	let temp_89_1 = (mul_((mul_(d, d)), (mul_(d, d))));
	assert(eq_(temp_89_0, temp_89_1)) by {
		lemma_eq_ref(temp_89_0);
	}
	let temp_90_0 = (mul_((mod_((mul_(d, a)), m)), (mul_((mod_(b, m)), b))));
	let temp_90_1 = (mul_((mul_((mod_((mul_(d, a)), m)), (mod_(b, m)))), b));
	assert(eq_(temp_90_0, temp_90_1)) by {
		lemma_mul_assoc(mod_(mul_(d, a), m), mod_(b, m), b);
	}
	let temp_91_0 = (mul_((mul_((mod_(a, m)), a)), (mul_(a, b))));
	let temp_91_1 = (mul_((mod_(a, m)), (mul_(a, (mul_(a, b))))));
	assert(eq_(temp_91_0, temp_91_1)) by {
		lemma_eq_sym(temp_91_1, temp_91_0);
		lemma_mul_assoc(mod_(a, m), a, mul_(a, b));
	}
	let temp_92_0 = (mul_((mul_(b, a)), (mod_((mul_(d, b)), m))));
	let temp_92_1 = (mul_((mul_(a, b)), (mod_((mul_(d, b)), m))));
	assert(eq_(temp_92_0, temp_92_1)) by {
		lemma_mul_comm(b, a);
		cong_mul_(mul_(b, a), mod_(mul_(d, b), m), mul_(a, b), mod_(mul_(d, b), m));
		lemma_eq_ref(mod_(mul_(d, b), m));
	}
	let temp_93_0 = (mod_((mul_((mul_(d, a)), (mul_(as_elem(28), d)))), m));
	let temp_93_1 = (mod_((mul_((mul_((mul_(d, a)), as_elem(28))), d)), m));
	assert(eq_(temp_93_0, temp_93_1)) by {
		lemma_mul_assoc(mul_(d, a), as_elem(28), d);
		cong_mod_(mul_(mul_(d, a), mul_(as_elem(28), d)), m, mul_(mul_(mul_(d, a), as_elem(28)), d), m);
		lemma_eq_ref(m);
	}
	let temp_94_0 = (mul_((mul_(a, a)), (mul_(c, c))));
	let temp_94_1 = (mul_(a, (mul_(a, (mul_(c, c))))));
	assert(eq_(temp_94_0, temp_94_1)) by {
		lemma_eq_sym(temp_94_1, temp_94_0);
		lemma_mul_assoc(a, a, mul_(c, c));
	}
	let temp_95_0 = (mul_((mul_(b, d)), (mul_(c, b))));
	let temp_95_1 = (mul_(b, (mul_(d, (mul_(c, b))))));
	assert(eq_(temp_95_0, temp_95_1)) by {
		lemma_eq_sym(temp_95_1, temp_95_0);
		lemma_mul_assoc(b, d, mul_(c, b));
	}
	let temp_96_0 = (sub_(b, (mul_(b, (mod_(a, m))))));
	let temp_96_1 = (sub_(b, (mul_(b, (mod_((add_(a, (mul_((add_((add_(c, d)), (mul_(b, c)))), m)))), m))))));
	assert(eq_(temp_96_0, temp_96_1)) by {
		lemma_mod_mul_vanish(a, add_(add_(c, d), mul_(b, c)), m);
		cong_sub_(b, mul_(b, mod_(a, m)), b, mul_(b, mod_(add_(a, mul_(add_(add_(c, d), mul_(b, c)), m)), m)));
		lemma_eq_ref(b);
		cong_mul_(b, mod_(a, m), b, mod_(add_(a, mul_(add_(add_(c, d), mul_(b, c)), m)), m));
	}
	let temp_97_0 = (mul_((mul_(a, b)), (mul_(c, b))));
	let temp_97_1 = (mul_((mul_((mul_(a, b)), c)), b));
	assert(eq_(temp_97_0, temp_97_1)) by {
		lemma_mul_assoc(mul_(a, b), c, b);
	}
	let temp_98_0 = (mul_((mul_(d, a)), (mul_(c, c))));
	let temp_98_1 = (mul_((mul_(a, d)), (mul_(c, c))));
	assert(eq_(temp_98_0, temp_98_1)) by {
		cong_mul_(mul_(d, a), mul_(c, c), mul_(a, d), mul_(c, c));
		lemma_mul_comm(d, a);
		lemma_mul_comm(c, c);
	}
	let temp_99_0 = (mul_((mul_(a, c)), (mul_(d, b))));
	let temp_99_1 = (mul_((mul_(c, a)), (mul_(d, b))));
	assert(eq_(temp_99_0, temp_99_1)) by {
		cong_mul_(mul_(a, c), mul_(d, b), mul_(c, a), mul_(d, b));
		lemma_mul_comm(a, c);
		lemma_eq_ref(mul_(d, b));
	}
	let temp_100_0 = (mul_((mul_(a, b)), (add_(b, as_elem(66)))));
	let temp_100_1 = (mul_((mul_(a, b)), (add_(as_elem(66), b))));
	assert(eq_(temp_100_0, temp_100_1)) by {
		lemma_add_comm(b, as_elem(66));
		cong_mul_(mul_(a, b), add_(b, as_elem(66)), mul_(a, b), add_(as_elem(66), b));
		lemma_eq_ref(mul_(a, b));
	}
	let temp_101_0 = (sub_((mul_(a, b)), (mul_((mod_(a, m)), c))));
	let temp_101_1 = (sub_((mul_(a, b)), (mul_(c, (mod_(a, m))))));
	assert(eq_(temp_101_0, temp_101_1)) by {
		lemma_mul_comm(mod_(a, m), c);
		cong_sub_(mul_(a, b), mul_(mod_(a, m), c), mul_(a, b), mul_(c, mod_(a, m)));
		lemma_eq_ref(mul_(a, b));
	}
	let temp_102_0 = (mul_((mul_(a, b)), (mul_(a, (mod_(a, m))))));
	let temp_102_1 = (mul_((mul_(b, a)), (mul_(a, (mod_(a, m))))));
	assert(eq_(temp_102_0, temp_102_1)) by {
		cong_mul_(mul_(a, b), mul_(a, mod_(a, m)), mul_(b, a), mul_(a, mod_(a, m)));
		lemma_mul_comm(a, b);
		lemma_eq_ref(mul_(a, mod_(a, m)));
	}
	let temp_103_0 = (sub_((mul_(a, b)), (mul_(d, a))));
	let temp_103_1 = (sub_((mul_(a, b)), (mul_(a, d))));
	assert(eq_(temp_103_0, temp_103_1)) by {
		cong_sub_(mul_(a, b), mul_(d, a), mul_(a, b), mul_(a, d));
		lemma_mul_comm(d, a);
		lemma_eq_ref(mul_(a, b));
	}
	let temp_104_0 = (mul_(a, (mul_((mod_(c, m)), (mod_(d, m))))));
	let temp_104_1 = (mul_((mul_(a, (mod_(c, m)))), (mod_(d, m))));
	assert(eq_(temp_104_0, temp_104_1)) by {
		lemma_mul_assoc(a, mod_(c, m), mod_(d, m));
	}
	let temp_105_0 = (mul_((mul_(d, b)), (add_(b, a))));
	let temp_105_1 = (mul_(d, (mul_(b, (add_(b, a))))));
	assert(eq_(temp_105_0, temp_105_1)) by {
		lemma_eq_sym(temp_105_1, temp_105_0);
		lemma_mul_assoc(d, b, add_(b, a));
	}
	let temp_106_0 = (mul_((mul_(a, d)), (mul_(d, c))));
	let temp_106_1 = (mul_((mul_((mul_(a, d)), d)), c));
	assert(eq_(temp_106_0, temp_106_1)) by {
		lemma_mul_assoc(mul_(a, d), d, c);
	}
	let temp_107_0 = (mul_((mod_((mul_(b, a)), m)), (mod_((mul_(c, (mod_(b, m)))), m))));
	let temp_107_1 = (mul_((mod_((mul_(b, a)), m)), (mod_((mul_((mod_(b, m)), c)), m))));
	assert(eq_(temp_107_0, temp_107_1)) by {
		lemma_mul_comm(c, mod_(b, m));
		cong_mul_(mod_(mul_(b, a), m), mod_(mul_(c, mod_(b, m)), m), mod_(mul_(b, a), m), mod_(mul_(mod_(b, m), c), m));
		lemma_eq_ref(mod_(mul_(b, a), m));
		cong_mod_(mul_(c, mod_(b, m)), m, mul_(mod_(b, m), c), m);
		lemma_eq_ref(m);
	}
	let temp_108_0 = (mul_((mul_(d, as_elem(84))), (sub_(b, (mod_(c, m))))));
	let temp_108_1 = (mul_((mul_(as_elem(84), d)), (sub_(b, (mod_(c, m))))));
	assert(eq_(temp_108_0, temp_108_1)) by {
		lemma_mul_comm(d, as_elem(84));
		cong_mul_(mul_(d, as_elem(84)), sub_(b, mod_(c, m)), mul_(as_elem(84), d), sub_(b, mod_(c, m)));
		lemma_eq_ref(sub_(b, mod_(c, m)));
	}
	let temp_109_0 = (mul_((mod_((mul_(c, d)), m)), (mod_((mul_(b, b)), m))));
	let temp_109_1 = (mul_((mod_((mul_(b, b)), m)), (mod_((mul_(c, d)), m))));
	assert(eq_(temp_109_0, temp_109_1)) by {
		lemma_mul_comm(mod_(mul_(c, d), m), mod_(mul_(b, b), m));
	}

}

} // verus!