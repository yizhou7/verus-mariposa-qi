use builtin_macros::*;
// use builtin::*;
mod nl_basics;
use crate::nl_basics::*;
verus! {

pub proof fn auto_0(a: Elem, b: Elem, c: Elem, d: Elem, m: Elem)
{
	let temp_0_0 = (mod_((mul_((sub_(b, c)), d)), m));
	let temp_0_1 = (mod_((sub_((mul_(b, d)), (mul_(c, d)))), m));
	assert(eq_(temp_0_0, temp_0_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_1_0 = (mod_((mul_((mul_(d, a)), (mul_(c, d)))), m));
	let temp_1_1 = (mod_((add_((mul_((mul_(d, a)), (mul_(c, d)))), (mul_((sub_((mul_(d, d)), (mul_(b, a)))), m)))), m));
	assert(eq_(temp_1_0, temp_1_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_2_0 = (mul_((mul_(a, a)), (mul_(c, d))));
	let temp_2_1 = (mul_((mul_(a, a)), (mul_(c, d))));
	assert(eq_(temp_2_0, temp_2_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_3_0 = (mul_((mul_((mod_(c, m)), b)), (mul_(b, c))));
	let temp_3_1 = (mul_((mul_((mod_((add_((mul_((mul_((mul_(b, b)), (mul_(d, (mod_(b, m)))))), m)), c)), m)), b)), (mul_(b, c))));
	assert(eq_(temp_3_0, temp_3_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_4_0 = (mul_((mul_(d, b)), (add_(b, b))));
	let temp_4_1 = (add_((mul_((mul_(d, b)), b)), (mul_((mul_(d, b)), b))));
	assert(eq_(temp_4_0, temp_4_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_5_0 = (mul_((mul_(a, b)), (mul_(b, a))));
	let temp_5_1 = (mul_((mul_((mul_(a, b)), b)), a));
	assert(eq_(temp_5_0, temp_5_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_6_0 = (mul_((mul_(d, a)), (mul_(d, c))));
	let temp_6_1 = (mul_((mul_((mul_(d, a)), d)), c));
	assert(eq_(temp_6_0, temp_6_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_7_0 = (add_((mul_(a, as_elem(58))), c));
	let temp_7_1 = (add_(c, (mul_(a, as_elem(58)))));
	assert(eq_(temp_7_0, temp_7_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_8_0 = (mod_((sub_((mul_(d, c)), (mul_(d, b)))), m));
	let temp_8_1 = (mod_((sub_((mul_(c, d)), (mul_(d, b)))), m));
	assert(eq_(temp_8_0, temp_8_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_9_0 = (sub_((mul_(d, c)), (mul_(b, d))));
	let temp_9_1 = (sub_((mul_(d, c)), (mul_(d, b))));
	assert(eq_(temp_9_0, temp_9_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_10_0 = (mul_((mul_(c, c)), (mul_(c, d))));
	let temp_10_1 = (mul_((mul_(c, c)), (mul_(c, d))));
	assert(eq_(temp_10_0, temp_10_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_11_0 = (sub_((mul_(a, b)), (mul_(b, a))));
	let temp_11_1 = (sub_((mul_(b, a)), (mul_(b, a))));
	assert(eq_(temp_11_0, temp_11_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_12_0 = (sub_((mod_((mul_(d, c)), m)), (add_(b, c))));
	let temp_12_1 = (sub_((mod_((mul_(d, c)), m)), (add_(c, b))));
	assert(eq_(temp_12_0, temp_12_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_13_0 = (mul_((mul_(c, c)), (mul_(d, d))));
	let temp_13_1 = (mul_(c, (mul_(c, (mul_(d, d))))));
	assert(eq_(temp_13_0, temp_13_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_14_0 = (mul_((mul_(d, b)), (mul_(c, b))));
	let temp_14_1 = (mul_((mul_((mul_(d, b)), c)), b));
	assert(eq_(temp_14_0, temp_14_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_15_0 = (mul_((mul_(d, b)), (mul_((mod_(c, m)), d))));
	let temp_15_1 = (mul_((mul_((mul_(d, b)), (mod_(c, m)))), d));
	assert(eq_(temp_15_0, temp_15_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_16_0 = (mul_((mul_(b, a)), (mul_(b, as_elem(87)))));
	let temp_16_1 = (mul_((mul_(b, as_elem(87))), (mul_(b, a))));
	assert(eq_(temp_16_0, temp_16_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_17_0 = (add_((mod_((mul_(c, b)), m)), (mul_(a, (mod_(b, m))))));
	let temp_17_1 = (add_((mul_(a, (mod_(b, m)))), (mod_((mul_(c, b)), m))));
	assert(eq_(temp_17_0, temp_17_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_18_0 = (mod_((sub_((mul_(d, (mod_(c, m)))), (mul_(a, as_elem(25))))), m));
	let temp_18_1 = (mod_((sub_((mul_(d, (mod_((add_((mul_((mul_((mul_(d, d)), (mul_(d, b)))), m)), c)), m)))), (mul_(a, as_elem(25))))), m));
	assert(eq_(temp_18_0, temp_18_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_19_0 = (mul_((mul_(c, c)), (mul_(b, d))));
	let temp_19_1 = (mul_(c, (mul_(c, (mul_(b, d))))));
	assert(eq_(temp_19_0, temp_19_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_20_0 = (mul_((sub_((mod_(a, m)), c)), (mul_(c, c))));
	let temp_20_1 = (sub_((mul_((mod_(a, m)), (mul_(c, c)))), (mul_(c, (mul_(c, c))))));
	assert(eq_(temp_20_0, temp_20_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_21_0 = (mul_((mul_(b, c)), (mod_((mul_(c, b)), m))));
	let temp_21_1 = (mul_(b, (mul_(c, (mod_((mul_(c, b)), m))))));
	assert(eq_(temp_21_0, temp_21_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_22_0 = (sub_((mod_((mul_((mod_(d, m)), d)), m)), (mul_(b, c))));
	let temp_22_1 = (sub_((mod_((mul_((mod_((sub_(d, (mul_((mul_((add_(d, c)), (mul_(c, c)))), m)))), m)), d)), m)), (mul_(b, c))));
	assert(eq_(temp_22_0, temp_22_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_23_0 = (mul_(c, (mul_(d, (mod_(a, m))))));
	let temp_23_1 = (mul_(c, (mul_(d, (mod_((add_(a, (mul_((add_((mul_(b, a)), (mul_(a, a)))), m)))), m))))));
	assert(eq_(temp_23_0, temp_23_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_24_0 = (add_((add_(c, a)), (mod_((mul_(d, b)), m))));
	let temp_24_1 = (add_((add_(c, a)), (mod_((mul_(b, d)), m))));
	assert(eq_(temp_24_0, temp_24_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_25_0 = (mul_((mul_(as_elem(58), b)), (mul_((mod_(as_elem(21), m)), b))));
	let temp_25_1 = (mul_((mul_(as_elem(58), b)), (mul_((mod_((sub_(as_elem(21), (mul_((mul_((mul_(d, b)), (mul_(c, d)))), m)))), m)), b))));
	assert(eq_(temp_25_0, temp_25_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_26_0 = (mul_((mul_(b, b)), (mul_(d, b))));
	let temp_26_1 = (mul_((mul_(b, b)), (mul_(d, b))));
	assert(eq_(temp_26_0, temp_26_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_27_0 = (mul_((mul_(b, a)), (add_((mod_(d, m)), c))));
	let temp_27_1 = (add_((mul_((mul_(b, a)), (mod_(d, m)))), (mul_((mul_(b, a)), c))));
	assert(eq_(temp_27_0, temp_27_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_28_0 = (mul_((sub_(b, b)), (mul_(c, a))));
	let temp_28_1 = (sub_((mul_(b, (mul_(c, a)))), (mul_(b, (mul_(c, a))))));
	assert(eq_(temp_28_0, temp_28_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_29_0 = (mul_((mul_(b, c)), (sub_(d, c))));
	let temp_29_1 = (mul_(b, (mul_(c, (sub_(d, c))))));
	assert(eq_(temp_29_0, temp_29_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_30_0 = (add_((mul_(c, b)), (mul_(b, d))));
	let temp_30_1 = (add_((mul_(b, d)), (mul_(c, b))));
	assert(eq_(temp_30_0, temp_30_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_31_0 = (mul_((mul_(a, c)), (mul_(b, (mod_(d, m))))));
	let temp_31_1 = (mul_((mul_(a, c)), (mul_((mod_(d, m)), b))));
	assert(eq_(temp_31_0, temp_31_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_32_0 = (mul_((mul_(a, a)), (mul_(c, a))));
	let temp_32_1 = (mul_((mul_(a, a)), (mul_(c, a))));
	assert(eq_(temp_32_0, temp_32_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_33_0 = (add_((mul_(d, b)), (mod_((mul_(a, (mod_(c, m)))), m))));
	let temp_33_1 = (add_((mul_(d, b)), (mod_((mul_((mod_(c, m)), a)), m))));
	assert(eq_(temp_33_0, temp_33_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_34_0 = (mul_((mul_(a, (mod_(b, m)))), (mul_(c, a))));
	let temp_34_1 = (mul_((mul_(a, (mod_((add_((mul_((mul_((mod_((mul_(d, a)), m)), (mul_(b, a)))), m)), b)), m)))), (mul_(c, a))));
	assert(eq_(temp_34_0, temp_34_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_35_0 = (mul_((add_(d, d)), (mul_(d, c))));
	let temp_35_1 = (add_((mul_(d, (mul_(d, c)))), (mul_(d, (mul_(d, c))))));
	assert(eq_(temp_35_0, temp_35_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_36_0 = (mul_((mul_((mod_(as_elem(64), m)), a)), (mul_(d, (mod_(c, m))))));
	let temp_36_1 = (mul_((mul_((mod_(as_elem(64), m)), a)), (mul_((mod_(c, m)), d))));
	assert(eq_(temp_36_0, temp_36_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_37_0 = (mul_((mod_((mul_(a, c)), m)), (mul_(as_elem(80), b))));
	let temp_37_1 = (mul_((mod_((add_((mul_(a, c)), (mul_((mul_((mul_(a, b)), (mul_(c, c)))), m)))), m)), (mul_(as_elem(80), b))));
	assert(eq_(temp_37_0, temp_37_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_38_0 = (mod_((mul_((mul_(c, a)), (mul_(b, c)))), m));
	let temp_38_1 = (mod_((mul_((mul_(b, c)), (mul_(c, a)))), m));
	assert(eq_(temp_38_0, temp_38_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_39_0 = (sub_((mul_(a, b)), (add_(b, a))));
	let temp_39_1 = (sub_((mul_(a, b)), (add_(a, b))));
	assert(eq_(temp_39_0, temp_39_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_40_0 = (mul_((mul_(c, d)), (mul_(d, b))));
	let temp_40_1 = (mul_((mul_(d, c)), (mul_(d, b))));
	assert(eq_(temp_40_0, temp_40_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_41_0 = (mod_((add_((mul_(c, c)), b)), m));
	let temp_41_1 = (mod_((add_((mul_(c, c)), b)), m));
	assert(eq_(temp_41_0, temp_41_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_42_0 = (mod_((mul_((mul_((mod_(b, m)), d)), (mul_(b, a)))), m));
	let temp_42_1 = (mod_((mul_((mul_((mod_((sub_(b, (mul_((mul_((sub_((mod_(c, m)), b)), (mul_((mod_(c, m)), b)))), m)))), m)), d)), (mul_(b, a)))), m));
	assert(eq_(temp_42_0, temp_42_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_43_0 = (mul_((sub_(b, d)), (mul_((mod_(a, m)), (mod_(b, m))))));
	let temp_43_1 = (sub_((mul_(b, (mul_((mod_(a, m)), (mod_(b, m)))))), (mul_(d, (mul_((mod_(a, m)), (mod_(b, m))))))));
	assert(eq_(temp_43_0, temp_43_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_44_0 = (mul_((mul_(c, d)), (mul_(b, a))));
	let temp_44_1 = (mul_((mul_(b, a)), (mul_(c, d))));
	assert(eq_(temp_44_0, temp_44_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_45_0 = (mul_((sub_(d, a)), (mul_(a, c))));
	let temp_45_1 = (mul_((sub_(d, a)), (mul_(c, a))));
	assert(eq_(temp_45_0, temp_45_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_46_0 = (mul_((mul_(c, b)), (mod_((mul_((mod_(c, m)), d)), m))));
	let temp_46_1 = (mul_((mul_(c, b)), (mod_((mul_(d, (mod_(c, m)))), m))));
	assert(eq_(temp_46_0, temp_46_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_47_0 = (mul_((mul_(a, c)), (sub_(d, b))));
	let temp_47_1 = (mul_((sub_(d, b)), (mul_(a, c))));
	assert(eq_(temp_47_0, temp_47_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_48_0 = (sub_((mul_(c, b)), (sub_((mod_(b, m)), a))));
	let temp_48_1 = (sub_((mul_(c, b)), (sub_((mod_((add_((mul_((mul_((mul_(a, as_elem(13))), (sub_(d, c)))), m)), b)), m)), a))));
	assert(eq_(temp_48_0, temp_48_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_49_0 = (mul_((add_(d, b)), (sub_(d, a))));
	let temp_49_1 = (add_((mul_(d, (sub_(d, a)))), (mul_(b, (sub_(d, a))))));
	assert(eq_(temp_49_0, temp_49_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_50_0 = (mul_((mul_(c, b)), (mul_(a, a))));
	let temp_50_1 = (mul_(c, (mul_(b, (mul_(a, a))))));
	assert(eq_(temp_50_0, temp_50_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_51_0 = (mul_((mul_(b, a)), (mul_(c, a))));
	let temp_51_1 = (mul_((mul_(b, a)), (mul_(a, c))));
	assert(eq_(temp_51_0, temp_51_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_52_0 = (mod_((add_((mod_((mul_(a, c)), m)), (mul_(c, b)))), m));
	let temp_52_1 = (mod_((add_((mod_((mul_(c, a)), m)), (mul_(c, b)))), m));
	assert(eq_(temp_52_0, temp_52_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_53_0 = (mul_((mod_((mul_(d, b)), m)), (mul_(b, b))));
	let temp_53_1 = (mul_((mul_((mod_((mul_(d, b)), m)), b)), b));
	assert(eq_(temp_53_0, temp_53_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_54_0 = (add_((mul_(b, a)), (mul_(b, b))));
	let temp_54_1 = (mul_(b, (add_(a, b))));
	assert(eq_(temp_54_0, temp_54_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_55_0 = (mul_((mul_(c, a)), (mul_(b, a))));
	let temp_55_1 = (mul_(c, (mul_(a, (mul_(b, a))))));
	assert(eq_(temp_55_0, temp_55_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_56_0 = (mul_((mul_(b, d)), (mod_((mul_(d, b)), m))));
	let temp_56_1 = (mul_((mod_((mul_(d, b)), m)), (mul_(b, d))));
	assert(eq_(temp_56_0, temp_56_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_57_0 = (mul_((mul_(a, d)), (mul_(a, c))));
	let temp_57_1 = (mul_((mul_((mul_(a, d)), a)), c));
	assert(eq_(temp_57_0, temp_57_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_58_0 = (mod_((add_((mul_(a, a)), (mul_(c, a)))), m));
	let temp_58_1 = (mod_((mul_((add_(a, c)), a)), m));
	assert(eq_(temp_58_0, temp_58_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_59_0 = (mul_((mul_(c, b)), (mul_(c, d))));
	let temp_59_1 = (mul_((mul_(b, c)), (mul_(c, d))));
	assert(eq_(temp_59_0, temp_59_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_60_0 = (add_((mod_((add_(a, d)), m)), (sub_(b, b))));
	let temp_60_1 = (add_((mod_((add_(d, a)), m)), (sub_(b, b))));
	assert(eq_(temp_60_0, temp_60_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_61_0 = (mul_((mul_(d, c)), (mod_((mul_(d, d)), m))));
	let temp_61_1 = (mul_((mul_(d, c)), (mod_((mul_(d, d)), m))));
	assert(eq_(temp_61_0, temp_61_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_62_0 = (mod_((sub_((mod_((mul_(a, b)), m)), (mul_(d, b)))), m));
	let temp_62_1 = (mod_((sub_((mod_((mul_(b, a)), m)), (mul_(d, b)))), m));
	assert(eq_(temp_62_0, temp_62_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_63_0 = (mul_((mul_(a, d)), (mul_(c, b))));
	let temp_63_1 = (mul_((mul_((mul_(a, d)), c)), b));
	assert(eq_(temp_63_0, temp_63_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_64_0 = (mul_((add_(a, d)), (mul_(b, c))));
	let temp_64_1 = (mul_((add_(a, d)), (mul_(c, b))));
	assert(eq_(temp_64_0, temp_64_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_65_0 = (mod_((mul_((mul_(a, a)), (mul_(b, a)))), m));
	let temp_65_1 = (mod_((mul_((mul_((mul_(a, a)), b)), a)), m));
	assert(eq_(temp_65_0, temp_65_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_66_0 = (mul_((mul_(d, a)), (mul_(d, b))));
	let temp_66_1 = (mul_((mul_(a, d)), (mul_(d, b))));
	assert(eq_(temp_66_0, temp_66_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_67_0 = (mul_((mul_(c, a)), (mul_(a, b))));
	let temp_67_1 = (mul_(c, (mul_(a, (mul_(a, b))))));
	assert(eq_(temp_67_0, temp_67_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_68_0 = (sub_((mul_(c, d)), (mod_(c, m))));
	let temp_68_1 = (sub_((mul_(c, d)), (mod_((sub_(c, (mul_((sub_((mul_(a, a)), (mul_(c, a)))), m)))), m))));
	assert(eq_(temp_68_0, temp_68_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_69_0 = (sub_((mul_((mod_(b, m)), a)), (mul_(b, b))));
	let temp_69_1 = (sub_((mul_((mod_((add_(b, (mul_((mul_((mul_(a, d)), (mul_(b, b)))), m)))), m)), a)), (mul_(b, b))));
	assert(eq_(temp_69_0, temp_69_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_70_0 = (mod_((mul_((mul_(d, d)), (mul_(b, a)))), m));
	let temp_70_1 = (mod_((mul_((mul_((mul_(d, d)), b)), a)), m));
	assert(eq_(temp_70_0, temp_70_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_71_0 = (mul_((add_((mod_(b, m)), d)), (mod_((mul_(a, (mod_(b, m)))), m))));
	let temp_71_1 = (add_((mul_((mod_(b, m)), (mod_((mul_(a, (mod_(b, m)))), m)))), (mul_(d, (mod_((mul_(a, (mod_(b, m)))), m))))));
	assert(eq_(temp_71_0, temp_71_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_72_0 = (mul_((mul_((mod_(d, m)), b)), (mul_(a, b))));
	let temp_72_1 = (mul_((mul_(a, b)), (mul_((mod_(d, m)), b))));
	assert(eq_(temp_72_0, temp_72_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_73_0 = (mul_((mul_((mod_(a, m)), c)), (mod_((add_(d, d)), m))));
	let temp_73_1 = (mul_((mul_((mod_(a, m)), c)), (mod_((add_((mul_((add_((mul_((mod_(a, m)), b)), (mul_(b, d)))), m)), (add_(d, d)))), m))));
	assert(eq_(temp_73_0, temp_73_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_74_0 = (mul_((mul_(a, d)), (sub_(d, c))));
	let temp_74_1 = (mul_(a, (mul_(d, (sub_(d, c))))));
	assert(eq_(temp_74_0, temp_74_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_75_0 = (mul_((add_(d, a)), (sub_(a, c))));
	let temp_75_1 = (mul_((sub_(a, c)), (add_(d, a))));
	assert(eq_(temp_75_0, temp_75_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_76_0 = (mul_((sub_(a, c)), (mul_(b, a))));
	let temp_76_1 = (mul_((mul_(b, a)), (sub_(a, c))));
	assert(eq_(temp_76_0, temp_76_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_77_0 = (sub_((sub_(c, d)), (mul_(c, a))));
	let temp_77_1 = (sub_((sub_(c, d)), (mul_(a, c))));
	assert(eq_(temp_77_0, temp_77_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_78_0 = (add_((mul_(d, (mod_(b, m)))), (sub_(b, c))));
	let temp_78_1 = (add_((sub_(b, c)), (mul_(d, (mod_(b, m))))));
	assert(eq_(temp_78_0, temp_78_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_79_0 = (mul_((mul_(c, b)), (mul_((mod_(d, m)), b))));
	let temp_79_1 = (mul_((mul_(c, b)), (mul_((mod_((sub_(d, (mul_((mul_((mul_(d, d)), d)), m)))), m)), b))));
	assert(eq_(temp_79_0, temp_79_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_80_0 = (mul_((mul_(b, b)), (mul_(c, c))));
	let temp_80_1 = (mul_((mul_(c, c)), (mul_(b, b))));
	assert(eq_(temp_80_0, temp_80_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_81_0 = (sub_((mul_(a, d)), (sub_(c, b))));
	let temp_81_1 = (sub_((mul_(d, a)), (sub_(c, b))));
	assert(eq_(temp_81_0, temp_81_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_82_0 = (add_((mul_(d, d)), (mod_((mul_(c, d)), m))));
	let temp_82_1 = (add_((mul_(d, d)), (mod_((mul_(d, c)), m))));
	assert(eq_(temp_82_0, temp_82_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_83_0 = (mod_((mul_((mul_(b, b)), (mul_(a, b)))), m));
	let temp_83_1 = (mod_((mul_((mul_(b, b)), (mul_(b, a)))), m));
	assert(eq_(temp_83_0, temp_83_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_84_0 = (mul_((mul_(a, (mod_(c, m)))), (mul_(b, a))));
	let temp_84_1 = (mul_((mul_(a, (mod_((sub_(c, (mul_((mul_((mul_(c, a)), (add_(c, c)))), m)))), m)))), (mul_(b, a))));
	assert(eq_(temp_84_0, temp_84_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_85_0 = (mul_((mul_(b, a)), (mul_((mod_(c, m)), as_elem(14)))));
	let temp_85_1 = (mul_((mul_((mul_(b, a)), (mod_(c, m)))), as_elem(14)));
	assert(eq_(temp_85_0, temp_85_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_86_0 = (mul_((mul_(d, as_elem(6))), (mul_(b, d))));
	let temp_86_1 = (mul_((mul_(d, as_elem(6))), (mul_(d, b))));
	assert(eq_(temp_86_0, temp_86_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_87_0 = (mod_((mul_((mul_(a, b)), (mul_(c, a)))), m));
	let temp_87_1 = (mod_((mul_((mul_(a, b)), (mul_(a, c)))), m));
	assert(eq_(temp_87_0, temp_87_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_88_0 = (mul_((mul_(b, (mod_(c, m)))), (mul_(as_elem(55), b))));
	let temp_88_1 = (mul_((mul_(b, (mod_(c, m)))), (mul_(b, as_elem(55)))));
	assert(eq_(temp_88_0, temp_88_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_89_0 = (mul_((mul_(a, d)), (mul_(d, b))));
	let temp_89_1 = (mul_(a, (mul_(d, (mul_(d, b))))));
	assert(eq_(temp_89_0, temp_89_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_90_0 = (mod_((mul_((mul_(a, b)), (mul_(a, c)))), m));
	let temp_90_1 = (mod_((add_((mul_((mul_((mul_(b, b)), (mul_((mod_(c, m)), d)))), m)), (mul_((mul_(a, b)), (mul_(a, c)))))), m));
	assert(eq_(temp_90_0, temp_90_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_91_0 = (mod_((mul_((mul_(c, d)), (mul_(d, b)))), m));
	let temp_91_1 = (mod_((add_((mul_((mod_((sub_((mul_(c, b)), (add_(a, a)))), m)), m)), (mul_((mul_(c, d)), (mul_(d, b)))))), m));
	assert(eq_(temp_91_0, temp_91_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_92_0 = (mul_((add_(d, b)), (mod_((mul_(c, d)), m))));
	let temp_92_1 = (mul_((add_(b, d)), (mod_((mul_(c, d)), m))));
	assert(eq_(temp_92_0, temp_92_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_93_0 = (mul_((sub_(d, d)), (add_(c, c))));
	let temp_93_1 = (mul_((sub_(d, d)), (add_(c, c))));
	assert(eq_(temp_93_0, temp_93_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_94_0 = (mul_((sub_(d, c)), (mul_(c, (mod_(c, m))))));
	let temp_94_1 = (mul_((mul_(c, (mod_(c, m)))), (sub_(d, c))));
	assert(eq_(temp_94_0, temp_94_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_95_0 = (mod_((add_((mul_((mod_(d, m)), (mod_(c, m)))), (mul_(c, b)))), m));
	let temp_95_1 = (mod_((add_((mul_((mod_(d, m)), (mod_(c, m)))), (mul_(b, c)))), m));
	assert(eq_(temp_95_0, temp_95_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_96_0 = (mod_((sub_((mul_(a, d)), (mul_(a, c)))), m));
	let temp_96_1 = (mod_((sub_((mul_(a, d)), (mod_((mul_(a, c)), m)))), m));
	assert(eq_(temp_96_0, temp_96_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_97_0 = (mul_((mul_(a, b)), (mul_(c, a))));
	let temp_97_1 = (mul_((mul_((mul_(a, b)), c)), a));
	assert(eq_(temp_97_0, temp_97_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_98_0 = (mul_((mul_(c, b)), (add_(c, a))));
	let temp_98_1 = (mul_(c, (mul_(b, (add_(c, a))))));
	assert(eq_(temp_98_0, temp_98_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_99_0 = (sub_((mul_(b, a)), (mul_(c, d))));
	let temp_99_1 = (sub_((mul_(a, b)), (mul_(c, d))));
	assert(eq_(temp_99_0, temp_99_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_100_0 = (mul_((mul_(c, c)), a));
	let temp_100_1 = (mul_(c, (mul_(c, a))));
	assert(eq_(temp_100_0, temp_100_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_101_0 = (add_((sub_((mod_(d, m)), d)), (mul_(b, c))));
	let temp_101_1 = (add_((sub_((mod_((add_((mul_((sub_((add_(b, b)), (mul_(d, d)))), m)), d)), m)), d)), (mul_(b, c))));
	assert(eq_(temp_101_0, temp_101_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_102_0 = (mul_((mul_(d, c)), (add_(c, c))));
	let temp_102_1 = (mul_((mul_(d, c)), (add_(c, c))));
	assert(eq_(temp_102_0, temp_102_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_103_0 = (add_((sub_(b, c)), (mul_(c, (mod_(b, m))))));
	let temp_103_1 = (add_((sub_(b, c)), (mul_(c, (mod_((add_(b, (mul_((mul_((mul_(d, a)), (mod_((add_(c, a)), m)))), m)))), m))))));
	assert(eq_(temp_103_0, temp_103_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_104_0 = (sub_((mul_(c, b)), (mul_(d, (mod_(a, m))))));
	let temp_104_1 = (sub_((mul_(b, c)), (mul_(d, (mod_(a, m))))));
	assert(eq_(temp_104_0, temp_104_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_105_0 = (mod_((mul_((mul_(c, d)), (mod_((mul_(b, b)), m)))), m));
	let temp_105_1 = (mod_((mod_((mul_((mul_(b, b)), (mul_(c, d)))), m)), m));
	assert(eq_(temp_105_0, temp_105_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_106_0 = (mod_((mul_((mul_(c, (mod_(c, m)))), (mod_((mul_(c, b)), m)))), m));
	let temp_106_1 = (mod_((mod_((mul_((mul_(c, (mod_(c, m)))), (mul_(c, b)))), m)), m));
	assert(eq_(temp_106_0, temp_106_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_107_0 = (mul_((mul_(b, d)), (mul_(b, c))));
	let temp_107_1 = (mul_(b, (mul_(d, (mul_(b, c))))));
	assert(eq_(temp_107_0, temp_107_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_108_0 = (sub_((mod_((mul_(b, d)), m)), (mul_(d, a))));
	let temp_108_1 = (sub_((mod_((mul_(b, d)), m)), (mul_(a, d))));
	assert(eq_(temp_108_0, temp_108_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_109_0 = (mul_((sub_((mod_(d, m)), d)), (mul_(b, (mod_(d, m))))));
	let temp_109_1 = (mul_((sub_((mod_(d, m)), d)), (mul_((mod_(d, m)), b))));
	assert(eq_(temp_109_0, temp_109_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_110_0 = (mul_((mul_((mod_(a, m)), b)), (add_((mod_(d, m)), b))));
	let temp_110_1 = (mul_((mod_(a, m)), (mul_(b, (add_((mod_(d, m)), b))))));
	assert(eq_(temp_110_0, temp_110_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_111_0 = (mul_((mod_((mul_(a, c)), m)), (mul_(b, c))));
	let temp_111_1 = (mul_((mod_((mul_(c, a)), m)), (mul_(b, c))));
	assert(eq_(temp_111_0, temp_111_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_112_0 = (mul_((mul_(a, (mod_(as_elem(77), m)))), (add_((mod_(a, m)), c))));
	let temp_112_1 = (mul_((mul_(a, (mod_(as_elem(77), m)))), (add_(c, (mod_(a, m))))));
	assert(eq_(temp_112_0, temp_112_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_113_0 = (mul_((mul_(a, a)), (mul_(d, b))));
	let temp_113_1 = (mul_(a, (mul_(a, (mul_(d, b))))));
	assert(eq_(temp_113_0, temp_113_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_114_0 = (add_((sub_(b, d)), (mul_(a, (mod_(d, m))))));
	let temp_114_1 = (add_((mul_(a, (mod_(d, m)))), (sub_(b, d))));
	assert(eq_(temp_114_0, temp_114_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_115_0 = (add_((mul_(c, a)), (sub_(c, b))));
	let temp_115_1 = (add_((mul_(a, c)), (sub_(c, b))));
	assert(eq_(temp_115_0, temp_115_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_116_0 = (sub_((mul_(a, a)), (mul_(b, c))));
	let temp_116_1 = (sub_((mul_(a, a)), (mul_(b, c))));
	assert(eq_(temp_116_0, temp_116_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_117_0 = (mul_((mul_(b, (mod_(d, m)))), (mul_(d, d))));
	let temp_117_1 = (mul_((mul_((mul_(b, (mod_(d, m)))), d)), d));
	assert(eq_(temp_117_0, temp_117_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_118_0 = (mul_((mul_(d, c)), (mod_((mul_(d, a)), m))));
	let temp_118_1 = (mul_((mul_(d, c)), (mod_((mul_(a, d)), m))));
	assert(eq_(temp_118_0, temp_118_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_119_0 = (mul_((mul_(c, b)), (mul_(b, a))));
	let temp_119_1 = (mul_((mul_(c, b)), (mul_(a, b))));
	assert(eq_(temp_119_0, temp_119_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_120_0 = (mul_((mul_(b, d)), (sub_(d, c))));
	let temp_120_1 = (mul_(b, (mul_(d, (sub_(d, c))))));
	assert(eq_(temp_120_0, temp_120_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_121_0 = (mul_((mul_(a, b)), (sub_(d, (mod_(c, m))))));
	let temp_121_1 = (mul_((mul_(a, b)), (sub_(d, (mod_((sub_(c, (mul_((mul_((mul_(a, c)), (mul_(d, c)))), m)))), m))))));
	assert(eq_(temp_121_0, temp_121_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_122_0 = (sub_((mul_(d, a)), (mul_(b, (mod_(b, m))))));
	let temp_122_1 = (sub_((mul_(d, a)), (mul_(b, (mod_((add_(b, (mul_((mod_((add_((mul_(a, c)), (mul_(b, b)))), m)), m)))), m))))));
	assert(eq_(temp_122_0, temp_122_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_123_0 = (mul_((mul_(a, c)), (add_(d, (mod_(d, m))))));
	let temp_123_1 = (mul_((mul_(a, c)), (add_(d, (mod_((add_((mul_((mul_((mul_(b, d)), (mul_((mod_(b, m)), d)))), m)), d)), m))))));
	assert(eq_(temp_123_0, temp_123_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_124_0 = (mul_(b, (mul_(d, d))));
	let temp_124_1 = (mul_((mul_(b, d)), d));
	assert(eq_(temp_124_0, temp_124_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_125_0 = (mul_((mul_(a, (mod_(c, m)))), (mul_(c, d))));
	let temp_125_1 = (mul_((mul_((mod_(c, m)), a)), (mul_(c, d))));
	assert(eq_(temp_125_0, temp_125_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_126_0 = (mul_((mod_((mul_(d, c)), m)), (mod_((mul_(d, a)), m))));
	let temp_126_1 = (mul_((mod_((sub_((mul_(d, c)), (mul_((mul_((mul_((mod_(d, m)), a)), (mul_(c, a)))), m)))), m)), (mod_((mul_(d, a)), m))));
	assert(eq_(temp_126_0, temp_126_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_127_0 = (mul_((add_(a, (mod_(b, m)))), (mul_(b, c))));
	let temp_127_1 = (mul_((add_((mod_(b, m)), a)), (mul_(b, c))));
	assert(eq_(temp_127_0, temp_127_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_128_0 = (mul_((add_(d, c)), (mul_(b, d))));
	let temp_128_1 = (mul_((add_(d, c)), (mul_(d, b))));
	assert(eq_(temp_128_0, temp_128_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_129_0 = (mul_((mul_((mod_(d, m)), a)), (mul_(b, c))));
	let temp_129_1 = (mul_((mul_((mul_((mod_(d, m)), a)), b)), c));
	assert(eq_(temp_129_0, temp_129_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_130_0 = (add_((mod_((mul_(b, a)), m)), (sub_(d, a))));
	let temp_130_1 = (add_((sub_(d, a)), (mod_((mul_(b, a)), m))));
	assert(eq_(temp_130_0, temp_130_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_131_0 = (mod_((mul_((mul_(b, b)), (mul_(b, b)))), m));
	let temp_131_1 = (mod_((mul_((mul_(b, b)), (mul_(b, b)))), m));
	assert(eq_(temp_131_0, temp_131_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_132_0 = (mul_((mul_(d, a)), (mul_(a, d))));
	let temp_132_1 = (mul_((mul_((mul_(d, a)), a)), d));
	assert(eq_(temp_132_0, temp_132_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_133_0 = (mul_((mul_(b, b)), (mod_((mul_(b, b)), m))));
	let temp_133_1 = (mul_(b, (mul_(b, (mod_((mul_(b, b)), m))))));
	assert(eq_(temp_133_0, temp_133_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_134_0 = (mul_((mul_(a, c)), (mul_(c, a))));
	let temp_134_1 = (mul_((mul_(c, a)), (mul_(c, a))));
	assert(eq_(temp_134_0, temp_134_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_135_0 = (mul_(c, (mul_(b, a))));
	let temp_135_1 = (mul_((mul_(c, b)), a));
	assert(eq_(temp_135_0, temp_135_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_136_0 = (mul_((mul_(d, c)), (mul_(as_elem(65), d))));
	let temp_136_1 = (mul_(d, (mul_(c, (mul_(as_elem(65), d))))));
	assert(eq_(temp_136_0, temp_136_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_137_0 = (mul_((mul_(d, a)), (mul_(a, b))));
	let temp_137_1 = (mul_((mul_(a, d)), (mul_(a, b))));
	assert(eq_(temp_137_0, temp_137_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_138_0 = (mul_((mul_(c, c)), (add_(c, as_elem(14)))));
	let temp_138_1 = (mul_((mul_(c, c)), (add_(as_elem(14), c))));
	assert(eq_(temp_138_0, temp_138_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_139_0 = (mul_((mul_(c, a)), (mul_(b, as_elem(31)))));
	let temp_139_1 = (mul_(c, (mul_(a, (mul_(b, as_elem(31)))))));
	assert(eq_(temp_139_0, temp_139_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_140_0 = (add_((mul_(as_elem(47), a)), (add_(a, (mod_(b, m))))));
	let temp_140_1 = (add_((mul_(a, as_elem(47))), (add_(a, (mod_(b, m))))));
	assert(eq_(temp_140_0, temp_140_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_141_0 = (mul_((mul_(a, a)), (mul_((mod_(b, m)), b))));
	let temp_141_1 = (mul_((mul_(a, a)), (mul_((mod_((add_((mul_((mul_((mul_(a, d)), (mul_(c, b)))), m)), b)), m)), b))));
	assert(eq_(temp_141_0, temp_141_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_142_0 = (mul_((mul_(d, a)), (mul_(c, d))));
	let temp_142_1 = (mul_((mul_(d, a)), (mul_(d, c))));
	assert(eq_(temp_142_0, temp_142_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_143_0 = (mul_((mul_(d, d)), (mul_(b, c))));
	let temp_143_1 = (mul_((mul_(b, c)), (mul_(d, d))));
	assert(eq_(temp_143_0, temp_143_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_144_0 = (mul_((mul_(a, c)), (mul_(c, b))));
	let temp_144_1 = (mul_((mul_(a, c)), (mul_(b, c))));
	assert(eq_(temp_144_0, temp_144_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_145_0 = (mul_((mul_((mod_(b, m)), d)), (mod_((mul_(b, d)), m))));
	let temp_145_1 = (mul_((mod_(b, m)), (mul_(d, (mod_((mul_(b, d)), m))))));
	assert(eq_(temp_145_0, temp_145_1)) by 
			{lemma_mul_properties_auto_1();}// 1

}

} // verus!