use builtin_macros::*;
// use builtin::*;
mod nl_basics;
use crate::nl_basics::*;
verus! {

pub proof fn auto_0(a: Elem, b: Elem, c: Elem, d: Elem, m: Elem)
{
	let temp_0_0 = (mul_((mul_(a, (mod_(a, m)))), (mul_(a, c))));
	let temp_0_1 = (mul_((mul_(a, (mod_((add_((mul_((mod_((add_(a, (mul_(a, d)))), m)), m)), a)), m)))), (mul_(a, c))));
	assert(eq_(temp_0_0, temp_0_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_1_0 = (mod_((mul_((mul_(c, b)), (mul_(c, (mod_(a, m)))))), m));
	let temp_1_1 = (mod_((mul_((mul_(b, c)), (mul_(c, (mod_(a, m)))))), m));
	assert(eq_(temp_1_0, temp_1_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_2_0 = (mul_((mod_((add_(a, b)), m)), (mul_(c, d))));
	let temp_2_1 = (mul_((mul_((mod_((add_(a, b)), m)), c)), d));
	assert(eq_(temp_2_0, temp_2_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_3_0 = (mul_((mul_(b, d)), a));
	let temp_3_1 = (mul_(b, (mul_(d, a))));
	assert(eq_(temp_3_0, temp_3_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_4_0 = (mul_((mul_(d, d)), (add_(c, (mod_(a, m))))));
	let temp_4_1 = (mul_((mul_(d, d)), (add_((mod_(a, m)), c))));
	assert(eq_(temp_4_0, temp_4_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_5_0 = (mul_((mul_(b, b)), (mul_(d, d))));
	let temp_5_1 = (mul_(b, (mul_(b, (mul_(d, d))))));
	assert(eq_(temp_5_0, temp_5_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_6_0 = (mul_((add_(c, a)), (mul_(b, (mod_(d, m))))));
	let temp_6_1 = (mul_((add_(c, a)), (mul_(b, (mod_((add_(d, (mul_((mul_((mul_(c, d)), (mul_(c, c)))), m)))), m))))));
	assert(eq_(temp_6_0, temp_6_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_7_0 = (mul_((mul_(c, (mod_(c, m)))), (mul_(b, b))));
	let temp_7_1 = (mul_((mul_(b, b)), (mul_(c, (mod_(c, m))))));
	assert(eq_(temp_7_0, temp_7_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_8_0 = (mul_((mul_(d, d)), (mul_(d, d))));
	let temp_8_1 = (mul_(d, (mul_(d, (mul_(d, d))))));
	assert(eq_(temp_8_0, temp_8_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_9_0 = (mul_((mod_((mul_(b, d)), m)), (mul_(d, (mod_(a, m))))));
	let temp_9_1 = (mul_((mod_((mul_(b, d)), m)), (mul_(d, (mod_((sub_(a, (mul_((mul_((mod_((sub_(a, c)), m)), (mul_(a, a)))), m)))), m))))));
	assert(eq_(temp_9_0, temp_9_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_10_0 = (mul_((mul_(a, c)), (mul_((mod_(c, m)), c))));
	let temp_10_1 = (mul_((mul_((mod_(c, m)), c)), (mul_(a, c))));
	assert(eq_(temp_10_0, temp_10_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_11_0 = (add_((mul_(d, c)), (mul_(b, a))));
	let temp_11_1 = (add_((mul_(b, a)), (mul_(d, c))));
	assert(eq_(temp_11_0, temp_11_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_12_0 = (mul_((mul_(a, c)), (add_(b, a))));
	let temp_12_1 = (add_((mul_((mul_(a, c)), b)), (mul_((mul_(a, c)), a))));
	assert(eq_(temp_12_0, temp_12_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_13_0 = (sub_((mul_(d, b)), (mul_(d, d))));
	let temp_13_1 = (sub_((mul_(d, b)), (mul_(d, d))));
	assert(eq_(temp_13_0, temp_13_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_14_0 = (mod_((sub_((mod_((mul_(b, d)), m)), (sub_(b, a)))), m));
	let temp_14_1 = (mod_((add_((mul_((mul_(a, (mul_(b, c)))), m)), (sub_((mod_((mul_(b, d)), m)), (sub_(b, a)))))), m));
	assert(eq_(temp_14_0, temp_14_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_15_0 = (mul_((mul_(a, a)), (mod_((mul_(a, c)), m))));
	let temp_15_1 = (mul_((mul_(a, a)), (mod_((mul_(a, c)), m))));
	assert(eq_(temp_15_0, temp_15_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_16_0 = (sub_((mul_(c, c)), (mul_(c, c))));
	let temp_16_1 = (sub_((mul_(c, c)), (mul_(c, c))));
	assert(eq_(temp_16_0, temp_16_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_17_0 = (mul_((mul_(a, b)), (mul_(a, a))));
	let temp_17_1 = (mul_((mul_(a, b)), (mul_(a, a))));
	assert(eq_(temp_17_0, temp_17_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_18_0 = (mul_((mul_(d, (mod_(d, m)))), (mul_(c, a))));
	let temp_18_1 = (mul_((mul_(d, (mod_((sub_(d, (mul_((mul_((mul_(d, d)), (mul_(d, d)))), m)))), m)))), (mul_(c, a))));
	assert(eq_(temp_18_0, temp_18_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_19_0 = (mul_((mul_((mod_(b, m)), (mod_(b, m)))), (mul_(c, c))));
	let temp_19_1 = (mul_((mul_((mod_(b, m)), (mod_(b, m)))), (mul_(c, c))));
	assert(eq_(temp_19_0, temp_19_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_20_0 = (mul_((mul_(b, b)), (mul_(c, a))));
	let temp_20_1 = (mul_((mul_(b, b)), (mul_(a, c))));
	assert(eq_(temp_20_0, temp_20_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_21_0 = (sub_((mul_(b, b)), (mul_(d, a))));
	let temp_21_1 = (sub_((mul_(b, b)), (mul_(a, d))));
	assert(eq_(temp_21_0, temp_21_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_22_0 = (mul_((add_(d, d)), (mul_((mod_(c, m)), (mod_(c, m))))));
	let temp_22_1 = (mul_((add_(d, d)), (mul_((mod_(c, m)), (mod_(c, m))))));
	assert(eq_(temp_22_0, temp_22_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_23_0 = (mul_((mul_(d, a)), (mul_(b, a))));
	let temp_23_1 = (mul_((mul_((mul_(d, a)), b)), a));
	assert(eq_(temp_23_0, temp_23_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_24_0 = (mul_((mul_(b, c)), (mul_(as_elem(55), (mod_(c, m))))));
	let temp_24_1 = (mul_((mul_(b, c)), (mul_(as_elem(55), (mod_((sub_(c, (mul_((sub_((mul_(b, d)), (mul_(d, (mod_(d, m)))))), m)))), m))))));
	assert(eq_(temp_24_0, temp_24_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_25_0 = (mul_((add_(b, c)), (mul_(a, b))));
	let temp_25_1 = (mul_((add_(c, b)), (mul_(a, b))));
	assert(eq_(temp_25_0, temp_25_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_26_0 = (add_((mul_(a, c)), (mul_(a, d))));
	let temp_26_1 = (add_((mul_(a, d)), (mul_(a, c))));
	assert(eq_(temp_26_0, temp_26_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_27_0 = (mul_((mul_(a, a)), (mul_(b, (mod_(d, m))))));
	let temp_27_1 = (mul_(a, (mul_(a, (mul_(b, (mod_(d, m))))))));
	assert(eq_(temp_27_0, temp_27_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_28_0 = (mul_((mul_(a, c)), (mul_(b, c))));
	let temp_28_1 = (mul_(a, (mul_(c, (mul_(b, c))))));
	assert(eq_(temp_28_0, temp_28_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_29_0 = (mul_((mul_(a, b)), (mul_(b, c))));
	let temp_29_1 = (mul_((mul_((mul_(a, b)), b)), c));
	assert(eq_(temp_29_0, temp_29_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_30_0 = (mul_((mul_(d, c)), (add_(a, b))));
	let temp_30_1 = (mul_((mul_(d, c)), (add_(b, a))));
	assert(eq_(temp_30_0, temp_30_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_31_0 = (add_((mul_(d, b)), (mod_(b, m))));
	let temp_31_1 = (add_((mod_(b, m)), (mul_(d, b))));
	assert(eq_(temp_31_0, temp_31_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_32_0 = (mul_((sub_(a, c)), (mul_(a, a))));
	let temp_32_1 = (sub_((mul_(a, (mul_(a, a)))), (mul_(c, (mul_(a, a))))));
	assert(eq_(temp_32_0, temp_32_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_33_0 = (mul_((mul_(b, b)), (mul_(c, b))));
	let temp_33_1 = (mul_(b, (mul_(b, (mul_(c, b))))));
	assert(eq_(temp_33_0, temp_33_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_34_0 = (mul_((mul_(d, d)), (mod_((mul_(a, a)), m))));
	let temp_34_1 = (mul_((mul_(d, d)), (mod_((add_((mul_((add_((mul_(a, b)), (mul_(d, d)))), m)), (mul_(a, a)))), m))));
	assert(eq_(temp_34_0, temp_34_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_35_0 = (mul_((mod_((add_(a, b)), m)), (sub_(d, c))));
	let temp_35_1 = (mul_((mod_((add_((add_(a, b)), (mul_((mul_((add_((mod_(a, m)), b)), (mul_(d, c)))), m)))), m)), (sub_(d, c))));
	assert(eq_(temp_35_0, temp_35_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_36_0 = (mul_((mul_(b, d)), (mul_(b, a))));
	let temp_36_1 = (mul_(b, (mul_(d, (mul_(b, a))))));
	assert(eq_(temp_36_0, temp_36_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_37_0 = (mul_((mul_(a, b)), (mul_(c, d))));
	let temp_37_1 = (mul_((mul_((mul_(a, b)), c)), d));
	assert(eq_(temp_37_0, temp_37_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_38_0 = (mul_((add_(a, b)), (mul_((mod_(d, m)), d))));
	let temp_38_1 = (mul_((mul_((add_(a, b)), (mod_(d, m)))), d));
	assert(eq_(temp_38_0, temp_38_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_39_0 = (mul_((mul_(d, d)), (mul_(b, c))));
	let temp_39_1 = (mul_((mul_(d, d)), (mul_(b, c))));
	assert(eq_(temp_39_0, temp_39_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_40_0 = (mul_((mul_(a, b)), (mul_(c, d))));
	let temp_40_1 = (mul_((mul_((mul_(a, b)), c)), d));
	assert(eq_(temp_40_0, temp_40_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_41_0 = (mul_((mul_(a, a)), (mod_((mul_(d, b)), m))));
	let temp_41_1 = (mul_((mul_(a, a)), (mod_((add_((mul_(d, b)), (mul_((mul_((mul_(c, c)), (mod_((mul_(b, (mod_(d, m)))), m)))), m)))), m))));
	assert(eq_(temp_41_0, temp_41_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_42_0 = (sub_((mul_(b, c)), (mul_(a, d))));
	let temp_42_1 = (sub_((mul_(c, b)), (mul_(a, d))));
	assert(eq_(temp_42_0, temp_42_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_43_0 = (mul_((add_(a, d)), (add_(b, a))));
	let temp_43_1 = (mul_((add_(d, a)), (add_(b, a))));
	assert(eq_(temp_43_0, temp_43_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_44_0 = (mul_((mul_(a, (mod_(a, m)))), (mul_(b, c))));
	let temp_44_1 = (mul_((mul_(a, (mod_(a, m)))), (mul_(c, b))));
	assert(eq_(temp_44_0, temp_44_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_45_0 = (mul_((mul_((mod_(d, m)), d)), (mul_(b, c))));
	let temp_45_1 = (mul_((mod_(d, m)), (mul_(d, (mul_(b, c))))));
	assert(eq_(temp_45_0, temp_45_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_46_0 = (mul_((mul_(as_elem(66), a)), (mul_(b, d))));
	let temp_46_1 = (mul_(as_elem(66), (mul_(a, (mul_(b, d))))));
	assert(eq_(temp_46_0, temp_46_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_47_0 = (add_((sub_(c, c)), (mul_(c, a))));
	let temp_47_1 = (add_((mul_(c, a)), (sub_(c, c))));
	assert(eq_(temp_47_0, temp_47_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_48_0 = (mul_((mul_(c, a)), (mul_(c, d))));
	let temp_48_1 = (mul_((mul_(c, d)), (mul_(c, a))));
	assert(eq_(temp_48_0, temp_48_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_49_0 = (mul_((mul_(c, c)), (mul_(c, c))));
	let temp_49_1 = (mul_(c, (mul_(c, (mul_(c, c))))));
	assert(eq_(temp_49_0, temp_49_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_50_0 = (mul_((mul_(b, d)), (mul_(a, c))));
	let temp_50_1 = (mul_((mul_(b, d)), (mul_(c, a))));
	assert(eq_(temp_50_0, temp_50_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_51_0 = (mul_((mul_(b, d)), (sub_(d, b))));
	let temp_51_1 = (mul_(b, (mul_(d, (sub_(d, b))))));
	assert(eq_(temp_51_0, temp_51_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_52_0 = (mul_((add_(a, a)), (mul_(d, c))));
	let temp_52_1 = (mul_((add_(a, a)), (mul_(c, d))));
	assert(eq_(temp_52_0, temp_52_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_53_0 = (mul_((mul_(d, a)), (mul_(a, c))));
	let temp_53_1 = (mul_((mul_(a, d)), (mul_(a, c))));
	assert(eq_(temp_53_0, temp_53_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_54_0 = (mul_((add_(c, d)), (mul_(c, (mod_(b, m))))));
	let temp_54_1 = (add_((mul_(c, (mul_(c, (mod_(b, m)))))), (mul_(d, (mul_(c, (mod_(b, m))))))));
	assert(eq_(temp_54_0, temp_54_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_55_0 = (mul_((mul_(as_elem(41), d)), (mul_(d, d))));
	let temp_55_1 = (mul_((mul_(d, d)), (mul_(as_elem(41), d))));
	assert(eq_(temp_55_0, temp_55_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_56_0 = (sub_((mul_(a, b)), (add_(a, a))));
	let temp_56_1 = (sub_((mul_(b, a)), (add_(a, a))));
	assert(eq_(temp_56_0, temp_56_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_57_0 = (add_((mul_((mod_(a, m)), c)), (mul_((mod_(c, m)), a))));
	let temp_57_1 = (add_((mul_(c, (mod_(a, m)))), (mul_((mod_(c, m)), a))));
	assert(eq_(temp_57_0, temp_57_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_58_0 = (mod_((sub_((mul_(b, a)), (add_(a, b)))), m));
	let temp_58_1 = (mod_((add_((mul_((mul_((mul_(a, b)), (mod_((mul_(d, c)), m)))), m)), (sub_((mul_(b, a)), (add_(a, b)))))), m));
	assert(eq_(temp_58_0, temp_58_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_59_0 = (add_((mod_((mul_(a, c)), m)), (add_(d, d))));
	let temp_59_1 = (add_((add_(d, d)), (mod_((mul_(a, c)), m))));
	assert(eq_(temp_59_0, temp_59_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_60_0 = (mul_((mod_((mul_(b, d)), m)), (add_(c, d))));
	let temp_60_1 = (mul_((mod_((add_((mul_((mul_((mul_(d, b)), (mul_(b, a)))), m)), (mul_(b, d)))), m)), (add_(c, d))));
	assert(eq_(temp_60_0, temp_60_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_61_0 = (mul_((mul_(a, c)), (mul_((mod_(c, m)), c))));
	let temp_61_1 = (mul_((mul_(a, c)), (mul_((mod_((add_((mul_((mul_((mul_(b, d)), (mul_((mod_(d, m)), (mod_(b, m)))))), m)), c)), m)), c))));
	assert(eq_(temp_61_0, temp_61_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_62_0 = (sub_((mul_(a, a)), (mul_(a, b))));
	let temp_62_1 = (sub_((mul_(a, a)), (mul_(a, b))));
	assert(eq_(temp_62_0, temp_62_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_63_0 = (mul_((mul_(d, b)), (mul_(a, d))));
	let temp_63_1 = (mul_((mul_(b, d)), (mul_(a, d))));
	assert(eq_(temp_63_0, temp_63_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_64_0 = (mul_((sub_(c, d)), (mul_(c, a))));
	let temp_64_1 = (mul_((mul_((sub_(c, d)), c)), a));
	assert(eq_(temp_64_0, temp_64_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_65_0 = (mul_((add_(a, b)), (mul_(a, d))));
	let temp_65_1 = (add_((mul_(a, (mul_(a, d)))), (mul_(b, (mul_(a, d))))));
	assert(eq_(temp_65_0, temp_65_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_66_0 = (mul_((mul_(d, a)), (mul_((mod_(d, m)), c))));
	let temp_66_1 = (mul_((mul_((mul_(d, a)), (mod_(d, m)))), c));
	assert(eq_(temp_66_0, temp_66_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_67_0 = (mod_((mul_((mul_(b, a)), (mul_(d, (mod_(c, m)))))), m));
	let temp_67_1 = (mod_((mul_((mul_(d, (mod_(c, m)))), (mul_(b, a)))), m));
	assert(eq_(temp_67_0, temp_67_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_68_0 = (mod_((add_((mul_(c, b)), (mul_(b, (mod_(a, m)))))), m));
	let temp_68_1 = (mod_((add_((mul_(b, c)), (mul_(b, (mod_(a, m)))))), m));
	assert(eq_(temp_68_0, temp_68_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_69_0 = (mod_((add_((mod_((mul_((mod_(b, m)), c)), m)), (mul_(b, c)))), m));
	let temp_69_1 = (mod_((add_((mod_((mod_((mul_((mod_(b, m)), c)), m)), m)), (mod_((mul_(b, c)), m)))), m));
	assert(eq_(temp_69_0, temp_69_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_70_0 = (mul_((mul_(d, b)), (mul_(a, d))));
	let temp_70_1 = (mul_((mul_(d, b)), (mul_(d, a))));
	assert(eq_(temp_70_0, temp_70_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_71_0 = (mod_((mul_((mul_(c, c)), (mul_(b, d)))), m));
	let temp_71_1 = (mod_((mul_((mul_(b, d)), (mul_(c, c)))), m));
	assert(eq_(temp_71_0, temp_71_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_72_0 = (mod_((mul_((mul_(c, a)), (mul_(b, c)))), m));
	let temp_72_1 = (mod_((mul_((mul_(c, a)), (mul_(c, b)))), m));
	assert(eq_(temp_72_0, temp_72_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_73_0 = (sub_((mul_(c, a)), (mul_(b, (mod_(c, m))))));
	let temp_73_1 = (sub_((mul_(c, a)), (mul_((mod_(c, m)), b))));
	assert(eq_(temp_73_0, temp_73_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_74_0 = (mul_((mul_(d, d)), (sub_(d, (mod_(b, m))))));
	let temp_74_1 = (mul_((mul_(d, d)), (sub_(d, (mod_(b, m))))));
	assert(eq_(temp_74_0, temp_74_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_75_0 = (mul_((mul_(a, d)), (mul_(c, (mod_(b, m))))));
	let temp_75_1 = (mul_(a, (mul_(d, (mul_(c, (mod_(b, m))))))));
	assert(eq_(temp_75_0, temp_75_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_76_0 = (mul_((mul_(c, c)), (mod_((mul_(b, b)), m))));
	let temp_76_1 = (mul_((mod_((mul_(b, b)), m)), (mul_(c, c))));
	assert(eq_(temp_76_0, temp_76_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_77_0 = (mul_((mul_(d, a)), (mul_(a, b))));
	let temp_77_1 = (mul_(d, (mul_(a, (mul_(a, b))))));
	assert(eq_(temp_77_0, temp_77_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_78_0 = (mod_((mul_((mul_(a, a)), (mul_(b, d)))), m));
	let temp_78_1 = (mod_((add_((mul_((mul_((sub_((mod_(c, m)), c)), (add_(a, d)))), m)), (mul_((mul_(a, a)), (mul_(b, d)))))), m));
	assert(eq_(temp_78_0, temp_78_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_79_0 = (sub_((add_(d, d)), (mul_(a, c))));
	let temp_79_1 = (sub_((add_(d, d)), (mul_(c, a))));
	assert(eq_(temp_79_0, temp_79_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_80_0 = (mul_((add_(a, b)), (mul_(b, c))));
	let temp_80_1 = (add_((mul_(a, (mul_(b, c)))), (mul_(b, (mul_(b, c))))));
	assert(eq_(temp_80_0, temp_80_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_81_0 = (mul_((sub_(b, a)), (sub_(c, c))));
	let temp_81_1 = (mul_((sub_(c, c)), (sub_(b, a))));
	assert(eq_(temp_81_0, temp_81_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_82_0 = (mul_((mul_(b, b)), (mul_(b, (mod_(d, m))))));
	let temp_82_1 = (mul_((mul_(b, b)), (mul_(b, (mod_((add_((mul_((mul_((add_(b, a)), (mul_(d, c)))), m)), d)), m))))));
	assert(eq_(temp_82_0, temp_82_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_83_0 = (mod_((mul_((mul_(b, b)), (mul_(d, c)))), m));
	let temp_83_1 = (mod_((mul_(b, (mul_(b, (mul_(d, c)))))), m));
	assert(eq_(temp_83_0, temp_83_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_84_0 = (mul_((mul_(c, a)), (mul_(c, b))));
	let temp_84_1 = (mul_((mul_(c, a)), (mul_(b, c))));
	assert(eq_(temp_84_0, temp_84_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_85_0 = (mul_((sub_(d, a)), (mul_(b, c))));
	let temp_85_1 = (sub_((mul_(d, (mul_(b, c)))), (mul_(a, (mul_(b, c))))));
	assert(eq_(temp_85_0, temp_85_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_86_0 = (mul_((mul_(c, d)), (mul_(c, d))));
	let temp_86_1 = (mul_((mul_(c, d)), (mul_(d, c))));
	assert(eq_(temp_86_0, temp_86_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_87_0 = (add_((mul_(c, a)), (mul_(d, as_elem(63)))));
	let temp_87_1 = (add_((mul_(c, a)), (mul_(as_elem(63), d))));
	assert(eq_(temp_87_0, temp_87_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_88_0 = (mul_((mod_((mul_(d, b)), m)), (mul_(a, b))));
	let temp_88_1 = (mul_((mod_((add_((mul_(d, b)), (mul_((mul_((mul_(d, a)), (sub_(b, d)))), m)))), m)), (mul_(a, b))));
	assert(eq_(temp_88_0, temp_88_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_89_0 = (mul_((add_(b, a)), (sub_(c, c))));
	let temp_89_1 = (mul_((add_(a, b)), (sub_(c, c))));
	assert(eq_(temp_89_0, temp_89_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_90_0 = (mul_((mul_(a, b)), (mod_((add_(b, b)), m))));
	let temp_90_1 = (mul_((mul_(a, b)), (mod_((sub_((add_(b, b)), (mul_((add_((mul_(d, b)), (mul_((mod_(a, m)), c)))), m)))), m))));
	assert(eq_(temp_90_0, temp_90_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_91_0 = (mul_((add_(d, (mod_(a, m)))), (add_(c, d))));
	let temp_91_1 = (add_((mul_((add_(d, (mod_(a, m)))), c)), (mul_((add_(d, (mod_(a, m)))), d))));
	assert(eq_(temp_91_0, temp_91_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_92_0 = (sub_((mul_(c, d)), (mul_((mod_(b, m)), d))));
	let temp_92_1 = (mul_((sub_(c, (mod_(b, m)))), d));
	assert(eq_(temp_92_0, temp_92_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_93_0 = (sub_((sub_(b, a)), (mul_(d, a))));
	let temp_93_1 = (sub_((sub_(b, a)), (mul_(a, d))));
	assert(eq_(temp_93_0, temp_93_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_94_0 = (mul_((mod_((mul_(b, (mod_(b, m)))), m)), (mul_(as_elem(100), a))));
	let temp_94_1 = (mul_((mul_((mod_((mul_(b, (mod_(b, m)))), m)), as_elem(100))), a));
	assert(eq_(temp_94_0, temp_94_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_95_0 = (add_((mul_((mod_(b, m)), c)), (mul_(c, c))));
	let temp_95_1 = (add_((mul_((mod_((sub_(b, (mul_((sub_((mul_(a, a)), (mul_(as_elem(40), (mod_(d, m)))))), m)))), m)), c)), (mul_(c, c))));
	assert(eq_(temp_95_0, temp_95_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_96_0 = (mul_((mul_(b, b)), (mul_(d, d))));
	let temp_96_1 = (mul_((mul_(b, b)), (mul_(d, d))));
	assert(eq_(temp_96_0, temp_96_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_97_0 = (mul_((sub_(a, b)), (mod_((sub_(d, b)), m))));
	let temp_97_1 = (mul_((sub_(a, b)), (mod_((sub_((mod_(d, m)), (mod_(b, m)))), m))));
	assert(eq_(temp_97_0, temp_97_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_98_0 = (add_((add_(c, d)), (mul_(b, c))));
	let temp_98_1 = (add_((mul_(b, c)), (add_(c, d))));
	assert(eq_(temp_98_0, temp_98_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_99_0 = (mul_((mul_(b, b)), (mod_((mul_(a, as_elem(67))), m))));
	let temp_99_1 = (mul_((mul_(b, b)), (mod_((add_((mul_(a, as_elem(67))), (mul_((mul_((mod_((mul_(d, a)), m)), (mul_(d, a)))), m)))), m))));
	assert(eq_(temp_99_0, temp_99_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_100_0 = (add_((mul_(d, (mod_(a, m)))), (mul_(c, c))));
	let temp_100_1 = (add_((mul_(d, (mod_(a, m)))), (mul_(c, c))));
	assert(eq_(temp_100_0, temp_100_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_101_0 = (mod_((mul_((sub_(a, a)), (mul_(d, c)))), m));
	let temp_101_1 = (mod_((sub_((mul_(a, (mul_(d, c)))), (mul_(a, (mul_(d, c)))))), m));
	assert(eq_(temp_101_0, temp_101_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_102_0 = (mul_((mul_(c, c)), (mul_(d, c))));
	let temp_102_1 = (mul_((mul_((mul_(c, c)), d)), c));
	assert(eq_(temp_102_0, temp_102_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_103_0 = (mul_((mul_(c, b)), (sub_(d, a))));
	let temp_103_1 = (mul_((mul_(b, c)), (sub_(d, a))));
	assert(eq_(temp_103_0, temp_103_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_104_0 = (mul_((mul_(b, a)), (mul_(b, a))));
	let temp_104_1 = (mul_((mul_(b, a)), (mul_(b, a))));
	assert(eq_(temp_104_0, temp_104_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_105_0 = (mul_((mul_(as_elem(13), b)), (mul_(c, b))));
	let temp_105_1 = (mul_(as_elem(13), (mul_(b, (mul_(c, b))))));
	assert(eq_(temp_105_0, temp_105_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_106_0 = (mul_(b, (mul_(b, c))));
	let temp_106_1 = (mul_((mul_(b, b)), c));
	assert(eq_(temp_106_0, temp_106_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_107_0 = (mul_((mul_((mod_(d, m)), d)), (sub_(d, d))));
	let temp_107_1 = (mul_((mul_((mod_((sub_(d, (mul_((mul_((mul_(d, (mod_(b, m)))), (add_(d, d)))), m)))), m)), d)), (sub_(d, d))));
	assert(eq_(temp_107_0, temp_107_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_108_0 = (add_((mul_(d, d)), (mul_(as_elem(71), (mod_(b, m))))));
	let temp_108_1 = (add_((mul_(as_elem(71), (mod_(b, m)))), (mul_(d, d))));
	assert(eq_(temp_108_0, temp_108_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_109_0 = (mul_((sub_(b, a)), (mod_((add_(b, a)), m))));
	let temp_109_1 = (mul_((sub_(b, a)), (mod_((add_((add_(b, a)), (mul_((mul_((mul_(a, b)), (mul_(b, c)))), m)))), m))));
	assert(eq_(temp_109_0, temp_109_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_110_0 = (mul_((mul_(c, d)), (mul_((mod_(d, m)), b))));
	let temp_110_1 = (mul_((mul_(d, c)), (mul_((mod_(d, m)), b))));
	assert(eq_(temp_110_0, temp_110_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_111_0 = (mul_((mul_(a, d)), (mul_(d, b))));
	let temp_111_1 = (mul_((mul_(a, d)), (mul_(b, d))));
	assert(eq_(temp_111_0, temp_111_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_112_0 = (mul_((mul_(b, c)), (sub_(b, a))));
	let temp_112_1 = (mul_((mul_(c, b)), (sub_(b, a))));
	assert(eq_(temp_112_0, temp_112_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_113_0 = (mod_((sub_((mul_(b, c)), (mul_(a, c)))), m));
	let temp_113_1 = (mod_((mul_((sub_(b, a)), c)), m));
	assert(eq_(temp_113_0, temp_113_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_114_0 = (mul_((sub_(b, d)), (sub_(b, as_elem(12)))));
	let temp_114_1 = (mul_((sub_(b, as_elem(12))), (sub_(b, d))));
	assert(eq_(temp_114_0, temp_114_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_115_0 = (add_((mul_(c, c)), (mul_(a, d))));
	let temp_115_1 = (add_((mul_(c, c)), (mul_(d, a))));
	assert(eq_(temp_115_0, temp_115_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_116_0 = (mul_((sub_(c, d)), (mul_(a, d))));
	let temp_116_1 = (mul_((mul_((sub_(c, d)), a)), d));
	assert(eq_(temp_116_0, temp_116_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_117_0 = (mul_((mul_((mod_(a, m)), c)), (mul_(c, d))));
	let temp_117_1 = (mul_((mul_((mod_(a, m)), c)), (mul_(d, c))));
	assert(eq_(temp_117_0, temp_117_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_118_0 = (mul_((mul_(c, b)), (mul_(as_elem(62), b))));
	let temp_118_1 = (mul_((mul_((mul_(c, b)), as_elem(62))), b));
	assert(eq_(temp_118_0, temp_118_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_119_0 = (mul_((mul_((mod_(a, m)), a)), (mul_(b, b))));
	let temp_119_1 = (mul_((mod_(a, m)), (mul_(a, (mul_(b, b))))));
	assert(eq_(temp_119_0, temp_119_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_120_0 = (mul_((mul_(d, b)), (mul_(c, d))));
	let temp_120_1 = (mul_((mul_(b, d)), (mul_(c, d))));
	assert(eq_(temp_120_0, temp_120_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_121_0 = (mul_((sub_(a, c)), (mod_((mul_((mod_(b, m)), (mod_(d, m)))), m))));
	let temp_121_1 = (mul_((sub_(a, c)), (mod_((mod_((mul_(d, (mod_(b, m)))), m)), m))));
	assert(eq_(temp_121_0, temp_121_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_122_0 = (mod_((mul_((sub_(d, b)), (sub_(a, as_elem(33))))), m));
	let temp_122_1 = (mod_((mul_((sub_(a, as_elem(33))), (sub_(d, b)))), m));
	assert(eq_(temp_122_0, temp_122_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_123_0 = (sub_((mul_(b, c)), (mul_(a, a))));
	let temp_123_1 = (sub_((mul_(c, b)), (mul_(a, a))));
	assert(eq_(temp_123_0, temp_123_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_124_0 = (mul_((mul_(d, c)), (mul_(c, (mod_(d, m))))));
	let temp_124_1 = (mul_((mul_(d, c)), (mul_((mod_(d, m)), c))));
	assert(eq_(temp_124_0, temp_124_1)) by 
			{lemma_mul_properties_auto_1();}// 1

}

} // verus!