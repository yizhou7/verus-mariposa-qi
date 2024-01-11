use builtin_macros::*;
// use builtin::*;
mod nl_basics;
use crate::nl_basics::*;
verus! {

pub proof fn auto_0(a: Elem, b: Elem, c: Elem, d: Elem, m: Elem)
{
	let temp_0_0 = (mul_((mul_(c, a)), (mod_((add_(b, c)), m))));
	let temp_0_1 = (mul_((mul_(a, c)), (mod_((add_(b, c)), m))));
	assert(eq_(temp_0_0, temp_0_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_1_0 = (mul_(d, (mul_(a, a))));
	let temp_1_1 = (mul_((mul_(a, a)), d));
	assert(eq_(temp_1_0, temp_1_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_2_0 = (mod_((mul_((mul_(d, a)), (mul_(c, (mod_(b, m)))))), m));
	let temp_2_1 = (mod_((mul_((mul_(d, a)), (mul_((mod_(b, m)), c)))), m));
	assert(eq_(temp_2_0, temp_2_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_3_0 = (mul_((add_(c, b)), (mod_((sub_(d, c)), m))));
	let temp_3_1 = (add_((mul_(c, (mod_((sub_(d, c)), m)))), (mul_(b, (mod_((sub_(d, c)), m))))));
	assert(eq_(temp_3_0, temp_3_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_4_0 = (mod_((mul_((mul_(a, b)), (mod_((mul_(a, b)), m)))), m));
	let temp_4_1 = (mod_((mul_(a, (mul_(b, (mod_((mul_(a, b)), m)))))), m));
	assert(eq_(temp_4_0, temp_4_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_5_0 = (mul_((mul_(b, d)), (mul_(b, c))));
	let temp_5_1 = (mul_((mul_(b, d)), (mul_(c, b))));
	assert(eq_(temp_5_0, temp_5_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_6_0 = (mod_((mul_((mul_(b, c)), (add_(c, d)))), m));
	let temp_6_1 = (mod_((mul_(b, (mul_(c, (add_(c, d)))))), m));
	assert(eq_(temp_6_0, temp_6_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_7_0 = (mul_((add_(c, (mod_(d, m)))), (mod_((add_(a, b)), m))));
	let temp_7_1 = (mul_((add_((mod_(d, m)), c)), (mod_((add_(a, b)), m))));
	assert(eq_(temp_7_0, temp_7_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_8_0 = (mul_((mul_(a, a)), (sub_(c, c))));
	let temp_8_1 = (mul_((mul_(a, a)), (sub_(c, c))));
	assert(eq_(temp_8_0, temp_8_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_9_0 = (mul_((add_(d, d)), (mod_((mul_(c, b)), m))));
	let temp_9_1 = (mul_((add_(d, d)), (mod_((sub_((mul_(c, b)), (mul_((mul_((mul_((mod_(a, m)), a)), (mul_(c, (mod_(c, m)))))), m)))), m))));
	assert(eq_(temp_9_0, temp_9_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_10_0 = (mul_((mul_(c, c)), (mod_((add_(as_elem(89), d)), m))));
	let temp_10_1 = (mul_((mul_(c, c)), (mod_((sub_((add_(as_elem(89), d)), (mul_((add_((mul_(a, b)), (mul_(d, (mod_(d, m)))))), m)))), m))));
	assert(eq_(temp_10_0, temp_10_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_11_0 = (mul_((mul_(a, b)), (mul_(d, a))));
	let temp_11_1 = (mul_(a, (mul_(b, (mul_(d, a))))));
	assert(eq_(temp_11_0, temp_11_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_12_0 = (mul_((mul_(d, (mod_(a, m)))), (mul_(b, as_elem(49)))));
	let temp_12_1 = (mul_((mul_((mod_(a, m)), d)), (mul_(b, as_elem(49)))));
	assert(eq_(temp_12_0, temp_12_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_13_0 = (mul_((mul_(a, (mod_(c, m)))), (mul_((mod_(d, m)), d))));
	let temp_13_1 = (mul_((mul_(a, (mod_(c, m)))), (mul_((mod_((add_(d, (mul_((mul_((mul_(a, b)), (mul_((mod_(a, m)), (mod_(b, m)))))), m)))), m)), d))));
	assert(eq_(temp_13_0, temp_13_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_14_0 = (mod_((mul_((mul_(b, d)), (mul_(c, a)))), m));
	let temp_14_1 = (mod_((mul_((mul_(c, a)), (mul_(b, d)))), m));
	assert(eq_(temp_14_0, temp_14_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_15_0 = (sub_((mul_(as_elem(96), c)), (mul_(d, d))));
	let temp_15_1 = (sub_((mul_(as_elem(96), c)), (mul_(d, d))));
	assert(eq_(temp_15_0, temp_15_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_16_0 = (mod_((mul_((mul_(d, c)), (mul_(b, c)))), m));
	let temp_16_1 = (mod_((add_((mul_((mul_((mul_(d, c)), (mul_(c, a)))), m)), (mul_((mul_(d, c)), (mul_(b, c)))))), m));
	assert(eq_(temp_16_0, temp_16_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_17_0 = (mod_((add_((mul_(b, a)), (mul_(a, b)))), m));
	let temp_17_1 = (mod_((add_((add_((mul_(b, a)), (mul_(a, b)))), (mul_((mul_((mod_((mul_(d, b)), m)), (mul_((mod_(b, m)), d)))), m)))), m));
	assert(eq_(temp_17_0, temp_17_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_18_0 = (add_((mul_(a, c)), (mul_(c, a))));
	let temp_18_1 = (add_((mul_(a, c)), (mul_(a, c))));
	assert(eq_(temp_18_0, temp_18_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_19_0 = (mul_((mul_(a, b)), (sub_(a, a))));
	let temp_19_1 = (mul_(a, (mul_(b, (sub_(a, a))))));
	assert(eq_(temp_19_0, temp_19_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_20_0 = (sub_(d, (mul_(b, a))));
	let temp_20_1 = (sub_(d, (mul_(a, b))));
	assert(eq_(temp_20_0, temp_20_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_21_0 = (mul_((add_(c, d)), (mul_(a, d))));
	let temp_21_1 = (mul_((add_(d, c)), (mul_(a, d))));
	assert(eq_(temp_21_0, temp_21_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_22_0 = (mod_((mul_((mod_((mul_(as_elem(69), a)), m)), (mul_(c, b)))), m));
	let temp_22_1 = (mod_((mul_((mul_((mod_((mul_(as_elem(69), a)), m)), c)), b)), m));
	assert(eq_(temp_22_0, temp_22_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_23_0 = (mul_((mul_(d, d)), (mul_(a, d))));
	let temp_23_1 = (mul_((mul_((mul_(d, d)), a)), d));
	assert(eq_(temp_23_0, temp_23_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_24_0 = (sub_((mul_(d, b)), (mul_(c, b))));
	let temp_24_1 = (sub_((mul_(d, b)), (mul_(b, c))));
	assert(eq_(temp_24_0, temp_24_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_25_0 = (mul_((add_(a, c)), (mul_((mod_(b, m)), a))));
	let temp_25_1 = (mul_((mul_((mod_(b, m)), a)), (add_(a, c))));
	assert(eq_(temp_25_0, temp_25_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_26_0 = (mul_((mul_(a, b)), (mul_(a, b))));
	let temp_26_1 = (mul_((mul_((mul_(a, b)), a)), b));
	assert(eq_(temp_26_0, temp_26_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_27_0 = (mul_((sub_(a, a)), (mul_((mod_(a, m)), d))));
	let temp_27_1 = (mul_((mul_((mod_(a, m)), d)), (sub_(a, a))));
	assert(eq_(temp_27_0, temp_27_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_28_0 = (mul_((add_(a, a)), (mul_(as_elem(54), c))));
	let temp_28_1 = (mul_((add_(a, a)), (mul_(as_elem(54), c))));
	assert(eq_(temp_28_0, temp_28_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_29_0 = (add_((mul_((mod_(c, m)), a)), (mul_(d, d))));
	let temp_29_1 = (add_((mul_((mod_(c, m)), a)), (mul_(d, d))));
	assert(eq_(temp_29_0, temp_29_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_30_0 = (mul_((mul_(c, c)), (mul_(b, a))));
	let temp_30_1 = (mul_((mul_(c, c)), (mul_(b, a))));
	assert(eq_(temp_30_0, temp_30_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_31_0 = (mul_((mod_((mul_(d, d)), m)), (mul_(b, b))));
	let temp_31_1 = (mul_((mod_((add_((mul_((mul_((mul_(a, c)), (mul_(c, (mod_(a, m)))))), m)), (mul_(d, d)))), m)), (mul_(b, b))));
	assert(eq_(temp_31_0, temp_31_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_32_0 = (mul_((mul_(d, a)), (add_(a, c))));
	let temp_32_1 = (mul_((mul_(d, a)), (add_(c, a))));
	assert(eq_(temp_32_0, temp_32_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_33_0 = (sub_((mul_(a, (mod_(a, m)))), (mul_((mod_(a, m)), d))));
	let temp_33_1 = (sub_((mul_(a, (mod_(a, m)))), (mul_(d, (mod_(a, m))))));
	assert(eq_(temp_33_0, temp_33_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_34_0 = (add_((add_(a, d)), (mul_(c, (mod_(c, m))))));
	let temp_34_1 = (add_((add_(d, a)), (mul_(c, (mod_(c, m))))));
	assert(eq_(temp_34_0, temp_34_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_35_0 = (mul_((add_(a, d)), (mod_((add_(a, d)), m))));
	let temp_35_1 = (mul_((mod_((add_(a, d)), m)), (add_(a, d))));
	assert(eq_(temp_35_0, temp_35_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_36_0 = (mul_((mod_((mul_(d, a)), m)), (mul_(a, a))));
	let temp_36_1 = (mul_((mod_((sub_((mul_(d, a)), (mul_((mul_((mul_((mod_(a, m)), a)), (mul_(c, d)))), m)))), m)), (mul_(a, a))));
	assert(eq_(temp_36_0, temp_36_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_37_0 = (mul_((mul_(a, a)), (mul_(c, c))));
	let temp_37_1 = (mul_((mul_((mul_(a, a)), c)), c));
	assert(eq_(temp_37_0, temp_37_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_38_0 = (mul_((add_(a, c)), (mul_(d, c))));
	let temp_38_1 = (add_((mul_(a, (mul_(d, c)))), (mul_(c, (mul_(d, c))))));
	assert(eq_(temp_38_0, temp_38_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_39_0 = (sub_((add_(d, c)), (mul_(c, c))));
	let temp_39_1 = (sub_((add_(d, c)), (mul_(c, c))));
	assert(eq_(temp_39_0, temp_39_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_40_0 = (mul_((sub_(c, b)), (sub_(d, a))));
	let temp_40_1 = (mul_((sub_(d, a)), (sub_(c, b))));
	assert(eq_(temp_40_0, temp_40_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_41_0 = (mul_((mul_((mod_(c, m)), b)), (mul_((mod_(c, m)), c))));
	let temp_41_1 = (mul_((mul_((mod_(c, m)), b)), (mul_((mod_((add_((mul_((mul_((mul_(d, (mod_(b, m)))), (sub_(b, (mod_(a, m)))))), m)), c)), m)), c))));
	assert(eq_(temp_41_0, temp_41_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_42_0 = (mod_((mul_((mul_(c, b)), (mul_(a, a)))), m));
	let temp_42_1 = (mod_((mul_(c, (mul_(b, (mul_(a, a)))))), m));
	assert(eq_(temp_42_0, temp_42_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_43_0 = (sub_((add_(b, c)), (add_(d, b))));
	let temp_43_1 = (sub_((add_(b, c)), (add_(b, d))));
	assert(eq_(temp_43_0, temp_43_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_44_0 = (mul_((mul_(as_elem(55), d)), (mul_(a, d))));
	let temp_44_1 = (mul_(as_elem(55), (mul_(d, (mul_(a, d))))));
	assert(eq_(temp_44_0, temp_44_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_45_0 = (mul_((mul_(c, a)), (add_(b, (mod_(b, m))))));
	let temp_45_1 = (add_((mul_((mul_(c, a)), b)), (mul_((mul_(c, a)), (mod_(b, m))))));
	assert(eq_(temp_45_0, temp_45_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_46_0 = (mul_((mod_((mul_(a, c)), m)), (sub_(c, b))));
	let temp_46_1 = (mul_((mod_((add_((mul_((mul_((mul_(b, a)), (mod_((mul_(a, (mod_(b, m)))), m)))), m)), (mul_(a, c)))), m)), (sub_(c, b))));
	assert(eq_(temp_46_0, temp_46_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_47_0 = (mul_((mul_(b, (mod_(c, m)))), (mod_((add_(b, a)), m))));
	let temp_47_1 = (mul_((mul_(b, (mod_(c, m)))), (mod_((add_((add_(b, a)), (mul_((mod_((sub_((mod_((mul_((mod_(b, m)), a)), m)), (mod_((mul_((mod_(b, m)), a)), m)))), m)), m)))), m))));
	assert(eq_(temp_47_0, temp_47_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_48_0 = (mul_((mul_(d, d)), (mul_(as_elem(54), d))));
	let temp_48_1 = (mul_(d, (mul_(d, (mul_(as_elem(54), d))))));
	assert(eq_(temp_48_0, temp_48_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_49_0 = (mod_((mul_((mod_((mul_(a, as_elem(51))), m)), (mod_(b, m)))), m));
	let temp_49_1 = (mod_((mul_((mod_((mul_(as_elem(51), a)), m)), (mod_(b, m)))), m));
	assert(eq_(temp_49_0, temp_49_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_50_0 = (mul_((mul_(b, (mod_(a, m)))), (mul_(b, a))));
	let temp_50_1 = (mul_((mul_(b, (mod_(a, m)))), (mul_(a, b))));
	assert(eq_(temp_50_0, temp_50_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_51_0 = (add_((add_(a, d)), (sub_(b, c))));
	let temp_51_1 = (add_((add_(d, a)), (sub_(b, c))));
	assert(eq_(temp_51_0, temp_51_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_52_0 = (mod_((add_((mul_(b, c)), (mul_(b, b)))), m));
	let temp_52_1 = (mod_((mul_(b, (add_(c, b)))), m));
	assert(eq_(temp_52_0, temp_52_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_53_0 = (mul_((sub_(c, d)), (mod_((add_(c, (mod_(d, m)))), m))));
	let temp_53_1 = (mul_((sub_(c, d)), (mod_((add_((mod_(d, m)), c)), m))));
	assert(eq_(temp_53_0, temp_53_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_54_0 = (mul_((mul_(b, c)), (mod_((mul_((mod_(b, m)), c)), m))));
	let temp_54_1 = (mul_((mod_((mul_((mod_(b, m)), c)), m)), (mul_(b, c))));
	assert(eq_(temp_54_0, temp_54_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_55_0 = (mod_((mul_((mod_((mul_(c, a)), m)), (mul_(b, b)))), m));
	let temp_55_1 = (mod_((mul_((mul_((mod_((mul_(c, a)), m)), b)), b)), m));
	assert(eq_(temp_55_0, temp_55_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_56_0 = (mul_((mul_(a, (mod_(c, m)))), (add_((mod_(a, m)), b))));
	let temp_56_1 = (mul_((mul_(a, (mod_(c, m)))), (add_(b, (mod_(a, m))))));
	assert(eq_(temp_56_0, temp_56_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_57_0 = (mul_((mul_(b, (mod_(a, m)))), d));
	let temp_57_1 = (mul_(b, (mul_((mod_(a, m)), d))));
	assert(eq_(temp_57_0, temp_57_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_58_0 = (add_((mod_((mul_(b, a)), m)), (mul_(d, as_elem(40)))));
	let temp_58_1 = (add_((mul_(d, as_elem(40))), (mod_((mul_(b, a)), m))));
	assert(eq_(temp_58_0, temp_58_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_59_0 = (sub_((mul_(d, d)), (mul_(b, c))));
	let temp_59_1 = (sub_((mul_(d, d)), (mul_(c, b))));
	assert(eq_(temp_59_0, temp_59_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_60_0 = (mul_((mul_(d, c)), (mod_((add_(a, a)), m))));
	let temp_60_1 = (mul_((mul_(d, c)), (mod_((add_(a, (mod_(a, m)))), m))));
	assert(eq_(temp_60_0, temp_60_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_61_0 = (add_((mul_(b, (mod_(b, m)))), (mul_(d, a))));
	let temp_61_1 = (add_((mul_(d, a)), (mul_(b, (mod_(b, m))))));
	assert(eq_(temp_61_0, temp_61_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_62_0 = (mul_((mul_(c, c)), (mul_(a, a))));
	let temp_62_1 = (mul_((mul_((mul_(c, c)), a)), a));
	assert(eq_(temp_62_0, temp_62_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_63_0 = (mul_((mul_(a, a)), (sub_(c, b))));
	let temp_63_1 = (mul_((sub_(c, b)), (mul_(a, a))));
	assert(eq_(temp_63_0, temp_63_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_64_0 = (mul_((mul_(a, c)), (mul_(c, b))));
	let temp_64_1 = (mul_(a, (mul_(c, (mul_(c, b))))));
	assert(eq_(temp_64_0, temp_64_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_65_0 = (add_((mul_(c, d)), (add_(b, b))));
	let temp_65_1 = (add_((add_(b, b)), (mul_(c, d))));
	assert(eq_(temp_65_0, temp_65_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_66_0 = (mul_((mod_((mul_(c, a)), m)), (mul_(c, d))));
	let temp_66_1 = (mul_((mul_((mod_((mul_(c, a)), m)), c)), d));
	assert(eq_(temp_66_0, temp_66_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_67_0 = (mul_((mul_(b, (mod_(b, m)))), (add_(b, a))));
	let temp_67_1 = (mul_((mul_((mod_(b, m)), b)), (add_(b, a))));
	assert(eq_(temp_67_0, temp_67_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_68_0 = (mul_((mul_(d, b)), (mul_(b, c))));
	let temp_68_1 = (mul_((mul_(b, d)), (mul_(b, c))));
	assert(eq_(temp_68_0, temp_68_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_69_0 = (mul_((mul_(c, c)), (mul_(b, a))));
	let temp_69_1 = (mul_((mul_(b, a)), (mul_(c, c))));
	assert(eq_(temp_69_0, temp_69_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_70_0 = (sub_((mul_(b, c)), (mul_(d, a))));
	let temp_70_1 = (sub_((mul_(c, b)), (mul_(d, a))));
	assert(eq_(temp_70_0, temp_70_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_71_0 = (add_((mul_(c, a)), (add_(b, a))));
	let temp_71_1 = (add_((add_(b, a)), (mul_(c, a))));
	assert(eq_(temp_71_0, temp_71_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_72_0 = (mul_((mul_(as_elem(68), a)), (mul_((mod_(a, m)), a))));
	let temp_72_1 = (mul_(as_elem(68), (mul_(a, (mul_((mod_(a, m)), a))))));
	assert(eq_(temp_72_0, temp_72_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_73_0 = (mul_((mul_(d, a)), (mul_((mod_(a, m)), b))));
	let temp_73_1 = (mul_((mul_((mul_(d, a)), (mod_(a, m)))), b));
	assert(eq_(temp_73_0, temp_73_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_74_0 = (add_((mul_(c, (mod_(a, m)))), (add_(c, c))));
	let temp_74_1 = (add_((mul_((mod_(a, m)), c)), (add_(c, c))));
	assert(eq_(temp_74_0, temp_74_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_75_0 = (mul_((mul_(b, (mod_(c, m)))), (mul_(a, b))));
	let temp_75_1 = (mul_(b, (mul_((mod_(c, m)), (mul_(a, b))))));
	assert(eq_(temp_75_0, temp_75_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_76_0 = (mul_((mul_(b, b)), (mul_(a, d))));
	let temp_76_1 = (mul_((mul_(b, b)), (mul_(d, a))));
	assert(eq_(temp_76_0, temp_76_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_77_0 = (mul_((mul_(d, c)), (add_(d, b))));
	let temp_77_1 = (mul_((mul_(c, d)), (add_(d, b))));
	assert(eq_(temp_77_0, temp_77_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_78_0 = (mod_((mul_((mul_((mod_(b, m)), b)), (mod_((sub_(b, a)), m)))), m));
	let temp_78_1 = (mod_((mul_((mul_((mod_(b, m)), b)), (mod_((sub_((mod_(b, m)), (mod_(a, m)))), m)))), m));
	assert(eq_(temp_78_0, temp_78_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_79_0 = (add_((sub_(c, d)), (add_(d, d))));
	let temp_79_1 = (add_((add_(d, d)), (sub_(c, d))));
	assert(eq_(temp_79_0, temp_79_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_80_0 = (add_((mod_((mul_(d, a)), m)), (mul_(a, d))));
	let temp_80_1 = (add_((mod_((mul_(a, d)), m)), (mul_(a, d))));
	assert(eq_(temp_80_0, temp_80_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_81_0 = (mul_((mul_(c, b)), (mul_((mod_(a, m)), d))));
	let temp_81_1 = (mul_((mul_(b, c)), (mul_((mod_(a, m)), d))));
	assert(eq_(temp_81_0, temp_81_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_82_0 = (mul_((mul_(d, a)), (mul_(d, c))));
	let temp_82_1 = (mul_((mul_((mul_(d, a)), d)), c));
	assert(eq_(temp_82_0, temp_82_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_83_0 = (mod_((sub_((mod_((add_(d, d)), m)), (mul_(b, a)))), m));
	let temp_83_1 = (mod_((sub_((sub_((mod_((add_(d, d)), m)), (mul_(b, a)))), (mul_((mul_((mod_((mul_(c, as_elem(91))), m)), (mul_(d, d)))), m)))), m));
	assert(eq_(temp_83_0, temp_83_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_84_0 = (sub_((mul_(b, b)), (sub_(b, c))));
	let temp_84_1 = (sub_((mul_(b, b)), (sub_(b, c))));
	assert(eq_(temp_84_0, temp_84_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_85_0 = (mul_((sub_(c, b)), (mul_(d, d))));
	let temp_85_1 = (mul_((sub_(c, b)), (mul_(d, d))));
	assert(eq_(temp_85_0, temp_85_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_86_0 = (mul_((mul_(b, (mod_(b, m)))), (mul_(b, b))));
	let temp_86_1 = (mul_((mul_(b, (mod_(b, m)))), (mul_(b, b))));
	assert(eq_(temp_86_0, temp_86_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_87_0 = (mul_((mul_(b, d)), (mul_(d, d))));
	let temp_87_1 = (mul_((mul_(b, d)), (mul_(d, d))));
	assert(eq_(temp_87_0, temp_87_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_88_0 = (sub_((mod_((mul_((mod_(d, m)), b)), m)), (mul_(a, c))));
	let temp_88_1 = (sub_((mod_((mul_((mod_(d, m)), b)), m)), (mul_(c, a))));
	assert(eq_(temp_88_0, temp_88_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_89_0 = (mul_((mul_(c, (mod_(d, m)))), (mul_(b, b))));
	let temp_89_1 = (mul_((mul_((mul_(c, (mod_(d, m)))), b)), b));
	assert(eq_(temp_89_0, temp_89_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_90_0 = (mul_((mod_((mul_(b, c)), m)), (mul_(c, d))));
	let temp_90_1 = (mul_((mul_((mod_((mul_(b, c)), m)), c)), d));
	assert(eq_(temp_90_0, temp_90_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_91_0 = (mul_((mul_(b, b)), (mul_(b, d))));
	let temp_91_1 = (mul_((mul_(b, b)), (mul_(b, d))));
	assert(eq_(temp_91_0, temp_91_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_92_0 = (add_((mod_((mul_(d, a)), m)), (sub_((mod_(c, m)), a))));
	let temp_92_1 = (add_((mod_((sub_((mul_(d, a)), (mul_((mul_((mul_(a, b)), (mul_(b, a)))), m)))), m)), (sub_((mod_(c, m)), a))));
	assert(eq_(temp_92_0, temp_92_1)) by 
			{lemma_mul_properties_auto_1();}// 1

}

} // verus!