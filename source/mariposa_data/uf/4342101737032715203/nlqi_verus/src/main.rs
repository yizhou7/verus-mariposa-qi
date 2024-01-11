use builtin_macros::*;
// use builtin::*;
mod nl_basics;
use crate::nl_basics::*;
verus! {

pub proof fn auto_0(a: Elem, b: Elem, c: Elem, d: Elem, m: Elem)
{
	let temp_0_0 = (mul_((mul_(a, b)), (mul_(b, (mod_(a, m))))));
	let temp_0_1 = (mul_((mul_(b, (mod_(a, m)))), (mul_(a, b))));
	assert(eq_(temp_0_0, temp_0_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_1_0 = (add_((mul_(b, c)), (mul_(b, a))));
	let temp_1_1 = (add_((mul_(b, a)), (mul_(b, c))));
	assert(eq_(temp_1_0, temp_1_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_2_0 = (mul_((mul_(c, a)), (mul_(d, c))));
	let temp_2_1 = (mul_(c, (mul_(a, (mul_(d, c))))));
	assert(eq_(temp_2_0, temp_2_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_3_0 = (mul_((mul_(b, b)), (mul_(b, d))));
	let temp_3_1 = (mul_(b, (mul_(b, (mul_(b, d))))));
	assert(eq_(temp_3_0, temp_3_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_4_0 = (mul_((mul_(c, a)), (mul_(b, (mod_(d, m))))));
	let temp_4_1 = (mul_((mul_((mul_(c, a)), b)), (mod_(d, m))));
	assert(eq_(temp_4_0, temp_4_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_5_0 = (mul_((mul_(a, b)), (sub_(c, d))));
	let temp_5_1 = (mul_(a, (mul_(b, (sub_(c, d))))));
	assert(eq_(temp_5_0, temp_5_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_6_0 = (mul_((mod_((mul_(a, a)), m)), (mul_(c, c))));
	let temp_6_1 = (mul_((mod_((add_((mul_((mul_((add_(c, d)), (mul_((mod_(d, m)), c)))), m)), (mul_(a, a)))), m)), (mul_(c, c))));
	assert(eq_(temp_6_0, temp_6_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_7_0 = (mul_((mul_(a, a)), (mod_((mul_((mod_(d, m)), a)), m))));
	let temp_7_1 = (mul_((mul_(a, a)), (mod_((mul_((mod_(d, m)), a)), m))));
	assert(eq_(temp_7_0, temp_7_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_8_0 = (mul_((add_(b, a)), (mul_(b, b))));
	let temp_8_1 = (mul_((mul_((add_(b, a)), b)), b));
	assert(eq_(temp_8_0, temp_8_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_9_0 = (mul_((add_(a, c)), (mod_((sub_(a, (mod_(c, m)))), m))));
	let temp_9_1 = (mul_((add_(a, c)), (mod_((sub_((mod_(a, m)), (mod_(c, m)))), m))));
	assert(eq_(temp_9_0, temp_9_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_10_0 = (mul_((mul_(b, (mod_(a, m)))), (mul_(b, b))));
	let temp_10_1 = (mul_((mul_(b, b)), (mul_(b, (mod_(a, m))))));
	assert(eq_(temp_10_0, temp_10_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_11_0 = (mod_((mul_((mul_(a, c)), (mul_(a, (mod_(d, m)))))), m));
	let temp_11_1 = (mod_((mul_((mul_(a, c)), (mul_(a, (mod_((sub_(d, (mul_((add_((mul_(a, d)), b)), m)))), m)))))), m));
	assert(eq_(temp_11_0, temp_11_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_12_0 = (mul_((mul_(d, (mod_(b, m)))), (mul_(a, a))));
	let temp_12_1 = (mul_((mul_(a, a)), (mul_(d, (mod_(b, m))))));
	assert(eq_(temp_12_0, temp_12_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_13_0 = (sub_(d, (mul_(c, b))));
	let temp_13_1 = (sub_(d, (mul_(b, c))));
	assert(eq_(temp_13_0, temp_13_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_14_0 = (add_((mul_((mod_(d, m)), c)), (mul_(b, a))));
	let temp_14_1 = (add_((mul_((mod_((add_((mul_((mul_((mul_(c, b)), (mul_(b, a)))), m)), d)), m)), c)), (mul_(b, a))));
	assert(eq_(temp_14_0, temp_14_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_15_0 = (mul_((mul_(c, b)), (mul_(a, b))));
	let temp_15_1 = (mul_((mul_(b, c)), (mul_(a, b))));
	assert(eq_(temp_15_0, temp_15_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_16_0 = (mul_((mul_(a, a)), (mod_((mul_(b, (mod_(a, m)))), m))));
	let temp_16_1 = (mul_((mul_(a, a)), (mod_((mul_(b, (mod_((add_(a, (mul_((add_((mul_(as_elem(60), a)), (add_(a, a)))), m)))), m)))), m))));
	assert(eq_(temp_16_0, temp_16_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_17_0 = (mul_((mul_(a, a)), (mul_(b, b))));
	let temp_17_1 = (mul_((mul_(b, b)), (mul_(a, a))));
	assert(eq_(temp_17_0, temp_17_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_18_0 = (mul_((mul_(b, a)), (add_(c, c))));
	let temp_18_1 = (mul_(b, (mul_(a, (add_(c, c))))));
	assert(eq_(temp_18_0, temp_18_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_19_0 = (add_((mul_(b, (mod_(d, m)))), (mul_(c, c))));
	let temp_19_1 = (add_((mul_(b, (mod_((add_(d, (mul_((mul_((mul_((mod_(b, m)), as_elem(53))), (mul_(d, (mod_(d, m)))))), m)))), m)))), (mul_(c, c))));
	assert(eq_(temp_19_0, temp_19_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_20_0 = (mod_((mul_((mul_(d, c)), (mul_(a, c)))), m));
	let temp_20_1 = (mod_((mul_(d, (mul_(c, (mul_(a, c)))))), m));
	assert(eq_(temp_20_0, temp_20_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_21_0 = (mul_((mul_(a, c)), (mul_(a, (mod_(c, m))))));
	let temp_21_1 = (mul_((mul_(a, c)), (mul_(a, (mod_((sub_(c, (mul_((mul_((mul_((mod_(b, m)), c)), (mul_(a, b)))), m)))), m))))));
	assert(eq_(temp_21_0, temp_21_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_22_0 = (mul_((mul_(c, c)), (mul_(b, as_elem(41)))));
	let temp_22_1 = (mul_((mul_(c, c)), (mul_(b, as_elem(41)))));
	assert(eq_(temp_22_0, temp_22_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_23_0 = (mul_((mul_(b, d)), (mul_(d, c))));
	let temp_23_1 = (mul_((mul_(d, c)), (mul_(b, d))));
	assert(eq_(temp_23_0, temp_23_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_24_0 = (mul_((sub_(d, d)), (mul_((mod_(b, m)), a))));
	let temp_24_1 = (mul_((mul_((sub_(d, d)), (mod_(b, m)))), a));
	assert(eq_(temp_24_0, temp_24_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_25_0 = (mul_((sub_(a, b)), (mul_(c, d))));
	let temp_25_1 = (mul_((mul_((sub_(a, b)), c)), d));
	assert(eq_(temp_25_0, temp_25_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_26_0 = (mul_((mul_(b, (mod_(a, m)))), (mod_((mul_(d, a)), m))));
	let temp_26_1 = (mul_((mul_(b, (mod_(a, m)))), (mod_((mul_(a, d)), m))));
	assert(eq_(temp_26_0, temp_26_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_27_0 = (mul_((mul_(c, b)), (mul_(d, a))));
	let temp_27_1 = (mul_(c, (mul_(b, (mul_(d, a))))));
	assert(eq_(temp_27_0, temp_27_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_28_0 = (add_((mul_(b, c)), (mul_(a, a))));
	let temp_28_1 = (add_((mul_(c, b)), (mul_(a, a))));
	assert(eq_(temp_28_0, temp_28_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_29_0 = (mul_((mul_((mod_(b, m)), a)), (mod_((mul_(d, (mod_(a, m)))), m))));
	let temp_29_1 = (mul_((mul_((mod_(b, m)), a)), (mod_((add_((mul_((mul_((sub_(c, (mod_(a, m)))), (mul_(a, a)))), m)), (mul_(d, (mod_(a, m)))))), m))));
	assert(eq_(temp_29_0, temp_29_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_30_0 = (mod_((mul_((mul_(a, b)), (mul_(d, a)))), m));
	let temp_30_1 = (mod_((mul_(a, (mul_(b, (mul_(d, a)))))), m));
	assert(eq_(temp_30_0, temp_30_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_31_0 = (mul_((mul_((mod_(c, m)), b)), (mod_((add_(c, b)), m))));
	let temp_31_1 = (mul_((mul_((mod_(c, m)), b)), (mod_((sub_((add_(c, b)), (mul_((mod_((add_((mod_((mul_(c, (mod_(c, m)))), m)), a)), m)), m)))), m))));
	assert(eq_(temp_31_0, temp_31_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_32_0 = (sub_((sub_(c, (mod_(as_elem(100), m)))), (add_(c, d))));
	let temp_32_1 = (sub_((sub_(c, (mod_((add_(as_elem(100), (mul_((mul_((mul_(as_elem(22), b)), (mul_(a, a)))), m)))), m)))), (add_(c, d))));
	assert(eq_(temp_32_0, temp_32_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_33_0 = (mul_((mod_((mul_(a, (mod_(a, m)))), m)), (mul_(a, a))));
	let temp_33_1 = (mul_((mod_((mul_(a, (mod_((sub_(a, (mul_((add_((add_(d, c)), (mod_((mul_(c, a)), m)))), m)))), m)))), m)), (mul_(a, a))));
	assert(eq_(temp_33_0, temp_33_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_34_0 = (mul_((mul_(d, as_elem(83))), (add_(b, b))));
	let temp_34_1 = (mul_((mul_(d, as_elem(83))), (add_(b, b))));
	assert(eq_(temp_34_0, temp_34_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_35_0 = (mul_((add_((mod_(c, m)), d)), (mul_(b, a))));
	let temp_35_1 = (mul_((add_((mod_((add_((mul_((mul_((mul_(d, d)), (add_(d, d)))), m)), c)), m)), d)), (mul_(b, a))));
	assert(eq_(temp_35_0, temp_35_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_36_0 = (mul_((mul_(a, d)), (add_(d, a))));
	let temp_36_1 = (mul_((mul_(a, d)), (add_(a, d))));
	assert(eq_(temp_36_0, temp_36_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_37_0 = (mul_((mod_((mul_(c, a)), m)), (mul_(c, (mod_(c, m))))));
	let temp_37_1 = (mul_((mul_((mod_((mul_(c, a)), m)), c)), (mod_(c, m))));
	assert(eq_(temp_37_0, temp_37_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_38_0 = (mul_((mul_(d, (mod_(a, m)))), (mul_(c, b))));
	let temp_38_1 = (mul_((mul_(d, (mod_((sub_(a, (mul_((mul_((mul_(a, b)), (mod_((add_(d, a)), m)))), m)))), m)))), (mul_(c, b))));
	assert(eq_(temp_38_0, temp_38_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_39_0 = (mul_((add_(c, b)), (mul_(a, d))));
	let temp_39_1 = (add_((mul_(c, (mul_(a, d)))), (mul_(b, (mul_(a, d))))));
	assert(eq_(temp_39_0, temp_39_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_40_0 = (mul_((mul_(as_elem(59), b)), (mul_(a, c))));
	let temp_40_1 = (mul_(as_elem(59), (mul_(b, (mul_(a, c))))));
	assert(eq_(temp_40_0, temp_40_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_41_0 = (add_((mul_(b, (mod_(a, m)))), (mod_((mul_(d, b)), m))));
	let temp_41_1 = (add_((mul_((mod_(a, m)), b)), (mod_((mul_(d, b)), m))));
	assert(eq_(temp_41_0, temp_41_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_42_0 = (mod_((add_((mul_((mod_(c, m)), d)), (mod_((mul_(b, b)), m)))), m));
	let temp_42_1 = (mod_((add_((mul_((mod_((sub_(c, (mul_((mul_((add_(c, b)), (mul_(a, b)))), m)))), m)), d)), (mod_((mul_(b, b)), m)))), m));
	assert(eq_(temp_42_0, temp_42_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_43_0 = (mul_((sub_(a, b)), (mod_((mul_(c, (mod_(c, m)))), m))));
	let temp_43_1 = (mul_((sub_(a, b)), (mod_((mod_((mul_(c, c)), m)), m))));
	assert(eq_(temp_43_0, temp_43_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_44_0 = (mul_((mul_(a, (mod_(d, m)))), (sub_(d, d))));
	let temp_44_1 = (mul_(a, (mul_((mod_(d, m)), (sub_(d, d))))));
	assert(eq_(temp_44_0, temp_44_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_45_0 = (sub_((mod_((mul_(a, as_elem(98))), m)), (mul_((mod_(a, m)), d))));
	let temp_45_1 = (sub_((mod_((mul_(a, as_elem(98))), m)), (mul_(d, (mod_(a, m))))));
	assert(eq_(temp_45_0, temp_45_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_46_0 = (mul_((sub_(b, d)), (mul_(d, c))));
	let temp_46_1 = (sub_((mul_(b, (mul_(d, c)))), (mul_(d, (mul_(d, c))))));
	assert(eq_(temp_46_0, temp_46_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_47_0 = (mul_((mul_(b, c)), (mul_(c, d))));
	let temp_47_1 = (mul_((mul_(c, b)), (mul_(c, d))));
	assert(eq_(temp_47_0, temp_47_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_48_0 = (mul_((mul_(d, b)), (mul_(d, a))));
	let temp_48_1 = (mul_((mul_(b, d)), (mul_(d, a))));
	assert(eq_(temp_48_0, temp_48_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_49_0 = (mul_((mul_(a, as_elem(41))), (mul_(a, b))));
	let temp_49_1 = (mul_(a, (mul_(as_elem(41), (mul_(a, b))))));
	assert(eq_(temp_49_0, temp_49_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_50_0 = (sub_((mul_((mod_(d, m)), a)), (mod_((mul_(b, d)), m))));
	let temp_50_1 = (sub_((mul_((mod_(d, m)), a)), (mod_((mul_(d, b)), m))));
	assert(eq_(temp_50_0, temp_50_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_51_0 = (sub_((mul_(c, a)), (mul_((mod_(b, m)), (mod_(c, m))))));
	let temp_51_1 = (sub_((mul_(c, a)), (mul_((mod_(b, m)), (mod_((add_(c, (mul_((add_((mul_(c, c)), (sub_(a, c)))), m)))), m))))));
	assert(eq_(temp_51_0, temp_51_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_52_0 = (mul_((mul_(a, d)), (mul_(a, b))));
	let temp_52_1 = (mul_((mul_(a, b)), (mul_(a, d))));
	assert(eq_(temp_52_0, temp_52_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_53_0 = (mod_((add_((mod_((add_(a, a)), m)), (mod_((mul_(b, c)), m)))), m));
	let temp_53_1 = (mod_((add_((mod_((add_(a, a)), m)), (mod_((mod_((mul_(b, c)), m)), m)))), m));
	assert(eq_(temp_53_0, temp_53_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_54_0 = (mod_((mul_((mul_(a, b)), (mul_(d, b)))), m));
	let temp_54_1 = (mod_((mul_((mul_(a, b)), (mul_(b, d)))), m));
	assert(eq_(temp_54_0, temp_54_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_55_0 = (mul_((mul_(d, (mod_(c, m)))), (mul_(d, (mod_(b, m))))));
	let temp_55_1 = (mul_((mul_(d, (mod_(c, m)))), (mul_(d, (mod_((add_((mul_((mod_((mul_((mul_(c, a)), (mod_((mul_(d, a)), m)))), m)), m)), b)), m))))));
	assert(eq_(temp_55_0, temp_55_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_56_0 = (mod_((mul_((mul_(a, a)), (sub_(d, c)))), m));
	let temp_56_1 = (mod_((mul_((sub_(d, c)), (mul_(a, a)))), m));
	assert(eq_(temp_56_0, temp_56_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_57_0 = (add_((sub_(b, a)), (sub_(c, d))));
	let temp_57_1 = (add_((sub_(c, d)), (sub_(b, a))));
	assert(eq_(temp_57_0, temp_57_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_58_0 = (mul_((mul_(b, c)), (mul_(a, (mod_(a, m))))));
	let temp_58_1 = (mul_((mul_(b, c)), (mul_((mod_(a, m)), a))));
	assert(eq_(temp_58_0, temp_58_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_59_0 = (mod_((mul_((mul_(d, c)), (mul_((mod_(b, m)), c)))), m));
	let temp_59_1 = (mod_((mul_((mul_(d, c)), (mul_((mod_((add_(b, (mul_((mod_((mul_((add_(c, c)), (mul_((mod_(a, m)), b)))), m)), m)))), m)), c)))), m));
	assert(eq_(temp_59_0, temp_59_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_60_0 = (mul_((mul_(b, b)), (mul_(a, c))));
	let temp_60_1 = (mul_(b, (mul_(b, (mul_(a, c))))));
	assert(eq_(temp_60_0, temp_60_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_61_0 = (mul_((mul_(a, b)), (mul_(b, b))));
	let temp_61_1 = (mul_((mul_(a, b)), (mul_(b, b))));
	assert(eq_(temp_61_0, temp_61_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_62_0 = (mul_((add_(d, c)), (sub_(c, d))));
	let temp_62_1 = (mul_((sub_(c, d)), (add_(d, c))));
	assert(eq_(temp_62_0, temp_62_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_63_0 = (sub_((mul_(d, a)), (mul_(a, d))));
	let temp_63_1 = (sub_((mul_(d, a)), (mul_(d, a))));
	assert(eq_(temp_63_0, temp_63_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_64_0 = (mod_((mul_((mul_(d, c)), (mul_(a, c)))), m));
	let temp_64_1 = (mod_((mul_((mul_(a, c)), (mul_(d, c)))), m));
	assert(eq_(temp_64_0, temp_64_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_65_0 = (mul_((mul_(b, b)), (mul_(d, d))));
	let temp_65_1 = (mul_(b, (mul_(b, (mul_(d, d))))));
	assert(eq_(temp_65_0, temp_65_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_66_0 = (add_((mod_((mul_(b, d)), m)), (mul_(c, d))));
	let temp_66_1 = (add_((mul_(c, d)), (mod_((mul_(b, d)), m))));
	assert(eq_(temp_66_0, temp_66_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_67_0 = (mul_((mul_((mod_(a, m)), a)), (sub_(d, d))));
	let temp_67_1 = (mul_((mul_((mod_((add_((mul_((mul_((mul_(b, c)), (mul_(a, c)))), m)), a)), m)), a)), (sub_(d, d))));
	assert(eq_(temp_67_0, temp_67_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_68_0 = (sub_((mul_(c, d)), (mul_(a, c))));
	let temp_68_1 = (sub_((mul_(c, d)), (mul_(c, a))));
	assert(eq_(temp_68_0, temp_68_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_69_0 = (mul_((mod_((mul_(a, b)), m)), a));
	let temp_69_1 = (mul_((mod_((sub_((mul_(a, b)), (mul_((sub_((add_((mod_(a, m)), c)), (sub_(b, b)))), m)))), m)), a));
	assert(eq_(temp_69_0, temp_69_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_70_0 = (mul_((mul_(c, b)), (mul_(d, a))));
	let temp_70_1 = (mul_((mul_(b, c)), (mul_(d, a))));
	assert(eq_(temp_70_0, temp_70_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_71_0 = (add_((mod_((mul_(a, b)), m)), (mul_(c, a))));
	let temp_71_1 = (add_((mod_((sub_((mul_(a, b)), (mul_((mul_((mul_(a, b)), (mul_(d, a)))), m)))), m)), (mul_(c, a))));
	assert(eq_(temp_71_0, temp_71_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_72_0 = (mul_((add_(a, c)), (mul_(d, d))));
	let temp_72_1 = (add_((mul_(a, (mul_(d, d)))), (mul_(c, (mul_(d, d))))));
	assert(eq_(temp_72_0, temp_72_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_73_0 = (mul_((sub_(c, d)), (mul_(a, (mod_(b, m))))));
	let temp_73_1 = (sub_((mul_(c, (mul_(a, (mod_(b, m)))))), (mul_(d, (mul_(a, (mod_(b, m))))))));
	assert(eq_(temp_73_0, temp_73_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_74_0 = (add_((mul_(b, d)), (mul_(a, d))));
	let temp_74_1 = (add_((mul_(a, d)), (mul_(b, d))));
	assert(eq_(temp_74_0, temp_74_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_75_0 = (mul_((mul_(c, a)), (mul_((mod_(d, m)), (mod_(b, m))))));
	let temp_75_1 = (mul_((mul_((mul_(c, a)), (mod_(d, m)))), (mod_(b, m))));
	assert(eq_(temp_75_0, temp_75_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_76_0 = (mul_((mul_(c, a)), (mul_(c, d))));
	let temp_76_1 = (mul_((mul_((mul_(c, a)), c)), d));
	assert(eq_(temp_76_0, temp_76_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_77_0 = (mul_((mul_(b, a)), (sub_(b, c))));
	let temp_77_1 = (mul_((sub_(b, c)), (mul_(b, a))));
	assert(eq_(temp_77_0, temp_77_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_78_0 = (mul_((mul_((mod_(d, m)), a)), (mul_(b, a))));
	let temp_78_1 = (mul_((mul_((mod_(d, m)), a)), (mul_(a, b))));
	assert(eq_(temp_78_0, temp_78_1)) by 
			{lemma_mul_properties_auto_1();}// 1

}

} // verus!