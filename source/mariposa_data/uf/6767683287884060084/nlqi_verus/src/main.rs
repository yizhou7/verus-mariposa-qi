use builtin_macros::*;
// use builtin::*;
mod nl_basics;
use crate::nl_basics::*;
verus! {

pub proof fn auto_0(a: Elem, b: Elem, c: Elem, d: Elem, m: Elem)
{
	let temp_0_0 = (mul_((mul_(c, d)), (add_(b, c))));
	let temp_0_1 = (add_((mul_((mul_(c, d)), b)), (mul_((mul_(c, d)), c))));
	assert(eq_(temp_0_0, temp_0_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_1_0 = (mul_((mul_(c, a)), (sub_(a, d))));
	let temp_1_1 = (mul_(c, (mul_(a, (sub_(a, d))))));
	assert(eq_(temp_1_0, temp_1_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_2_0 = (mul_((mul_(a, c)), (mul_(a, a))));
	let temp_2_1 = (mul_((mul_(a, c)), (mul_(a, a))));
	assert(eq_(temp_2_0, temp_2_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_3_0 = (mul_((add_(d, a)), (mul_(c, (mod_(b, m))))));
	let temp_3_1 = (mul_((add_(a, d)), (mul_(c, (mod_(b, m))))));
	assert(eq_(temp_3_0, temp_3_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_4_0 = (mul_((mul_(c, d)), (add_(d, d))));
	let temp_4_1 = (add_((mul_((mul_(c, d)), d)), (mul_((mul_(c, d)), d))));
	assert(eq_(temp_4_0, temp_4_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_5_0 = (mul_((mod_((mul_(b, d)), m)), (mul_(d, a))));
	let temp_5_1 = (mul_((mod_((add_((mul_((mul_((mul_(b, d)), (mod_((mul_(c, a)), m)))), m)), (mul_(b, d)))), m)), (mul_(d, a))));
	assert(eq_(temp_5_0, temp_5_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_6_0 = (mul_((mod_((mul_(a, a)), m)), (sub_(c, d))));
	let temp_6_1 = (mul_((mod_((mul_(a, a)), m)), (sub_(c, d))));
	assert(eq_(temp_6_0, temp_6_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_7_0 = (mul_((mul_(b, d)), (mul_(b, b))));
	let temp_7_1 = (mul_(b, (mul_(d, (mul_(b, b))))));
	assert(eq_(temp_7_0, temp_7_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_8_0 = (mul_((add_(b, a)), (mul_(d, d))));
	let temp_8_1 = (add_((mul_(b, (mul_(d, d)))), (mul_(a, (mul_(d, d))))));
	assert(eq_(temp_8_0, temp_8_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_9_0 = (add_((mul_(a, b)), (mul_(b, a))));
	let temp_9_1 = (add_((mul_(b, a)), (mul_(b, a))));
	assert(eq_(temp_9_0, temp_9_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_10_0 = (mul_((mul_(c, b)), (mul_(c, d))));
	let temp_10_1 = (mul_(c, (mul_(b, (mul_(c, d))))));
	assert(eq_(temp_10_0, temp_10_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_11_0 = (add_((mul_(b, c)), (mul_(a, b))));
	let temp_11_1 = (add_((mul_(b, c)), (mul_(b, a))));
	assert(eq_(temp_11_0, temp_11_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_12_0 = (add_((add_(a, c)), (mul_(c, c))));
	let temp_12_1 = (add_((add_(a, c)), (mul_(c, c))));
	assert(eq_(temp_12_0, temp_12_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_13_0 = (mod_((mul_((mul_((mod_(b, m)), b)), (mul_(c, a)))), m));
	let temp_13_1 = (mod_((mul_((mul_((mod_((add_((mul_((add_((mod_((mul_(d, a)), m)), (mul_(c, as_elem(79))))), m)), b)), m)), b)), (mul_(c, a)))), m));
	assert(eq_(temp_13_0, temp_13_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_14_0 = (sub_((mul_(as_elem(71), c)), (mul_(b, b))));
	let temp_14_1 = (sub_((mul_(c, as_elem(71))), (mul_(b, b))));
	assert(eq_(temp_14_0, temp_14_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_15_0 = (mul_((mul_(d, (mod_(d, m)))), (add_((mod_(a, m)), d))));
	let temp_15_1 = (mul_((mul_((mod_(d, m)), d)), (add_((mod_(a, m)), d))));
	assert(eq_(temp_15_0, temp_15_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_16_0 = (add_((mul_((mod_(b, m)), d)), (mul_(c, a))));
	let temp_16_1 = (add_((mul_((mod_((add_(b, (mul_((sub_((mul_(a, a)), (mul_(c, d)))), m)))), m)), d)), (mul_(c, a))));
	assert(eq_(temp_16_0, temp_16_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_17_0 = (mul_((mod_((sub_(c, b)), m)), (mul_(d, d))));
	let temp_17_1 = (mul_((mod_((add_((sub_(c, b)), (mul_((mul_((mul_(as_elem(11), a)), (sub_(c, b)))), m)))), m)), (mul_(d, d))));
	assert(eq_(temp_17_0, temp_17_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_18_0 = (mul_(b, (mul_(a, a))));
	let temp_18_1 = (mul_((mul_(b, a)), a));
	assert(eq_(temp_18_0, temp_18_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_19_0 = (sub_((mul_(c, d)), (sub_(c, as_elem(99)))));
	let temp_19_1 = (sub_((mul_(d, c)), (sub_(c, as_elem(99)))));
	assert(eq_(temp_19_0, temp_19_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_20_0 = (sub_((mul_(a, b)), (add_(c, d))));
	let temp_20_1 = (sub_((mul_(a, b)), (add_(d, c))));
	assert(eq_(temp_20_0, temp_20_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_21_0 = (mul_((mul_((mod_(b, m)), a)), (mul_(a, a))));
	let temp_21_1 = (mul_((mul_((mod_((add_((mul_((sub_((sub_(d, c)), (add_((mod_(b, m)), d)))), m)), b)), m)), a)), (mul_(a, a))));
	assert(eq_(temp_21_0, temp_21_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_22_0 = (mul_(a, (sub_(d, c))));
	let temp_22_1 = (mul_((sub_(d, c)), a));
	assert(eq_(temp_22_0, temp_22_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_23_0 = (mul_((mul_(d, d)), (mul_(b, b))));
	let temp_23_1 = (mul_(d, (mul_(d, (mul_(b, b))))));
	assert(eq_(temp_23_0, temp_23_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_24_0 = (mul_((sub_(a, d)), (mul_(c, c))));
	let temp_24_1 = (sub_((mul_(a, (mul_(c, c)))), (mul_(d, (mul_(c, c))))));
	assert(eq_(temp_24_0, temp_24_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_25_0 = (sub_((mul_(b, c)), (add_(d, b))));
	let temp_25_1 = (sub_((mul_(b, c)), (add_(b, d))));
	assert(eq_(temp_25_0, temp_25_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_26_0 = (mul_((mul_(d, c)), (mul_(a, a))));
	let temp_26_1 = (mul_((mul_((mul_(d, c)), a)), a));
	assert(eq_(temp_26_0, temp_26_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_27_0 = (mul_((mul_(c, b)), (mul_(c, c))));
	let temp_27_1 = (mul_((mul_(b, c)), (mul_(c, c))));
	assert(eq_(temp_27_0, temp_27_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_28_0 = (mul_((mul_(b, c)), (mul_(as_elem(94), d))));
	let temp_28_1 = (mul_((mul_(b, c)), (mul_(d, as_elem(94)))));
	assert(eq_(temp_28_0, temp_28_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_29_0 = (sub_((mul_(d, c)), (add_(c, c))));
	let temp_29_1 = (sub_((mul_(d, c)), (add_(c, c))));
	assert(eq_(temp_29_0, temp_29_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_30_0 = (mul_((mul_(a, c)), (mul_(b, b))));
	let temp_30_1 = (mul_((mul_(a, c)), (mul_(b, b))));
	assert(eq_(temp_30_0, temp_30_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_31_0 = (mul_((sub_(b, d)), (mul_(a, a))));
	let temp_31_1 = (mul_((mul_((sub_(b, d)), a)), a));
	assert(eq_(temp_31_0, temp_31_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_32_0 = (mul_((mul_(b, d)), (mul_(b, (mod_(a, m))))));
	let temp_32_1 = (mul_((mul_(b, d)), (mul_((mod_(a, m)), b))));
	assert(eq_(temp_32_0, temp_32_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_33_0 = (add_((mul_(a, c)), (sub_((mod_(c, m)), as_elem(82)))));
	let temp_33_1 = (add_((mul_(c, a)), (sub_((mod_(c, m)), as_elem(82)))));
	assert(eq_(temp_33_0, temp_33_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_34_0 = (mod_((mul_((mul_(b, d)), (mul_(c, d)))), m));
	let temp_34_1 = (mod_((add_((mul_((mul_((mul_(c, a)), (mod_((sub_(a, c)), m)))), m)), (mul_((mul_(b, d)), (mul_(c, d)))))), m));
	assert(eq_(temp_34_0, temp_34_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_35_0 = (mul_((mul_(d, a)), (mul_(a, a))));
	let temp_35_1 = (mul_(d, (mul_(a, (mul_(a, a))))));
	assert(eq_(temp_35_0, temp_35_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_36_0 = (add_((mul_((mod_(b, m)), a)), (sub_(a, a))));
	let temp_36_1 = (add_((mul_(a, (mod_(b, m)))), (sub_(a, a))));
	assert(eq_(temp_36_0, temp_36_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_37_0 = (mul_((mul_(d, d)), (mul_(a, a))));
	let temp_37_1 = (mul_((mul_(d, d)), (mul_(a, a))));
	assert(eq_(temp_37_0, temp_37_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_38_0 = (add_((mul_(b, b)), (add_(d, d))));
	let temp_38_1 = (add_((mul_(b, b)), (add_(d, d))));
	assert(eq_(temp_38_0, temp_38_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_39_0 = (mul_((mul_((mod_(b, m)), c)), (mul_(a, (mod_(as_elem(23), m))))));
	let temp_39_1 = (mul_((mul_(a, (mod_(as_elem(23), m)))), (mul_((mod_(b, m)), c))));
	assert(eq_(temp_39_0, temp_39_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_40_0 = (mul_(a, (sub_((mod_(c, m)), b))));
	let temp_40_1 = (mul_((sub_((mod_(c, m)), b)), a));
	assert(eq_(temp_40_0, temp_40_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_41_0 = (add_((mul_(d, d)), (mul_(b, (mod_(d, m))))));
	let temp_41_1 = (add_((mul_(b, (mod_(d, m)))), (mul_(d, d))));
	assert(eq_(temp_41_0, temp_41_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_42_0 = (mul_((mod_(b, m)), (mul_(d, c))));
	let temp_42_1 = (mul_((mod_((sub_(b, (mul_((mul_((mul_(c, d)), a)), m)))), m)), (mul_(d, c))));
	assert(eq_(temp_42_0, temp_42_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_43_0 = (sub_((mul_(d, c)), (mul_(c, c))));
	let temp_43_1 = (mul_((sub_(d, c)), c));
	assert(eq_(temp_43_0, temp_43_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_44_0 = (mul_((mul_(d, a)), (mul_(a, b))));
	let temp_44_1 = (mul_(d, (mul_(a, (mul_(a, b))))));
	assert(eq_(temp_44_0, temp_44_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_45_0 = (add_((mod_((mul_(b, c)), m)), (mul_(d, d))));
	let temp_45_1 = (add_((mod_((sub_((mul_(b, c)), (mul_((mul_((sub_(c, c)), (mul_(b, c)))), m)))), m)), (mul_(d, d))));
	assert(eq_(temp_45_0, temp_45_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_46_0 = (mul_((mul_(b, c)), (sub_(a, d))));
	let temp_46_1 = (mul_((mul_(c, b)), (sub_(a, d))));
	assert(eq_(temp_46_0, temp_46_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_47_0 = (mul_((mul_((mod_(c, m)), c)), (mul_(d, d))));
	let temp_47_1 = (mul_((mul_((mod_((add_((mul_((mod_((add_((mul_(d, (mod_(d, m)))), (mul_(a, d)))), m)), m)), c)), m)), c)), (mul_(d, d))));
	assert(eq_(temp_47_0, temp_47_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_48_0 = (mul_((mul_(d, (mod_(b, m)))), (add_(d, c))));
	let temp_48_1 = (mul_((mul_(d, (mod_((add_(b, (mul_((mul_((mul_(d, b)), c)), m)))), m)))), (add_(d, c))));
	assert(eq_(temp_48_0, temp_48_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_49_0 = (mul_((mod_((mul_(a, a)), m)), (add_(c, c))));
	let temp_49_1 = (add_((mul_((mod_((mul_(a, a)), m)), c)), (mul_((mod_((mul_(a, a)), m)), c))));
	assert(eq_(temp_49_0, temp_49_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_50_0 = (mul_((mul_(a, b)), (mul_(c, (mod_(c, m))))));
	let temp_50_1 = (mul_(a, (mul_(b, (mul_(c, (mod_(c, m))))))));
	assert(eq_(temp_50_0, temp_50_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_51_0 = (mul_((mul_(c, d)), (mul_(a, c))));
	let temp_51_1 = (mul_((mul_(a, c)), (mul_(c, d))));
	assert(eq_(temp_51_0, temp_51_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_52_0 = (mul_((mul_((mod_(b, m)), a)), (mul_(b, b))));
	let temp_52_1 = (mul_((mul_(b, b)), (mul_((mod_(b, m)), a))));
	assert(eq_(temp_52_0, temp_52_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_53_0 = (mul_((mul_(c, as_elem(62))), (add_(c, b))));
	let temp_53_1 = (mul_((add_(c, b)), (mul_(c, as_elem(62)))));
	assert(eq_(temp_53_0, temp_53_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_54_0 = (mul_((mul_((mod_(a, m)), c)), (mul_(d, c))));
	let temp_54_1 = (mul_((mul_((mod_((sub_(a, (mul_((mul_((mod_((mul_((mod_(d, m)), c)), m)), (mul_(c, b)))), m)))), m)), c)), (mul_(d, c))));
	assert(eq_(temp_54_0, temp_54_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_55_0 = (mod_((mul_((mod_((mul_(d, d)), m)), (mul_(b, c)))), m));
	let temp_55_1 = (mod_((mul_((mul_(b, c)), (mod_((mul_(d, d)), m)))), m));
	assert(eq_(temp_55_0, temp_55_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_56_0 = (mul_((mul_(d, d)), (mul_(b, d))));
	let temp_56_1 = (mul_(d, (mul_(d, (mul_(b, d))))));
	assert(eq_(temp_56_0, temp_56_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_57_0 = (mul_((mul_(c, b)), (mul_(a, a))));
	let temp_57_1 = (mul_((mul_(c, b)), (mul_(a, a))));
	assert(eq_(temp_57_0, temp_57_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_58_0 = (mul_((mod_((add_(c, d)), m)), (sub_(a, b))));
	let temp_58_1 = (mul_((sub_(a, b)), (mod_((add_(c, d)), m))));
	assert(eq_(temp_58_0, temp_58_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_59_0 = (mul_((mul_(a, c)), (mul_(b, a))));
	let temp_59_1 = (mul_(a, (mul_(c, (mul_(b, a))))));
	assert(eq_(temp_59_0, temp_59_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_60_0 = (mul_((mod_((mul_(a, c)), m)), (mul_(d, (mod_(b, m))))));
	let temp_60_1 = (mul_((mul_(d, (mod_(b, m)))), (mod_((mul_(a, c)), m))));
	assert(eq_(temp_60_0, temp_60_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_61_0 = (mul_((mul_(as_elem(60), a)), (mul_(d, a))));
	let temp_61_1 = (mul_((mul_((mul_(as_elem(60), a)), d)), a));
	assert(eq_(temp_61_0, temp_61_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_62_0 = (mul_((mul_((mod_(b, m)), a)), (mul_(b, b))));
	let temp_62_1 = (mul_((mod_(b, m)), (mul_(a, (mul_(b, b))))));
	assert(eq_(temp_62_0, temp_62_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_63_0 = (mul_((mod_((add_(as_elem(73), c)), m)), (mod_((mul_(b, d)), m))));
	let temp_63_1 = (mul_((mod_((add_(as_elem(73), c)), m)), (mod_((sub_((mul_(b, d)), (mul_((mul_((mul_(b, d)), (mul_(c, c)))), m)))), m))));
	assert(eq_(temp_63_0, temp_63_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_64_0 = (mul_((mul_(a, b)), (mul_(d, b))));
	let temp_64_1 = (mul_((mul_(b, a)), (mul_(d, b))));
	assert(eq_(temp_64_0, temp_64_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_65_0 = (add_((mul_((mod_(d, m)), b)), (mul_((mod_(a, m)), c))));
	let temp_65_1 = (add_((mul_((mod_(d, m)), b)), (mul_((mod_((add_(a, (mul_((add_((mul_(a, b)), (mul_((mod_(a, m)), b)))), m)))), m)), c))));
	assert(eq_(temp_65_0, temp_65_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_66_0 = (mul_((mul_(c, (mod_(d, m)))), (mul_(c, a))));
	let temp_66_1 = (mul_(c, (mul_((mod_(d, m)), (mul_(c, a))))));
	assert(eq_(temp_66_0, temp_66_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_67_0 = (mul_((mod_((add_(as_elem(37), c)), m)), (mul_(c, d))));
	let temp_67_1 = (mul_((mul_((mod_((add_(as_elem(37), c)), m)), c)), d));
	assert(eq_(temp_67_0, temp_67_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_68_0 = (mul_((mul_(a, a)), (mul_(d, b))));
	let temp_68_1 = (mul_((mul_(d, b)), (mul_(a, a))));
	assert(eq_(temp_68_0, temp_68_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_69_0 = (mul_((mul_(d, a)), (mul_(b, c))));
	let temp_69_1 = (mul_((mul_((mul_(d, a)), b)), c));
	assert(eq_(temp_69_0, temp_69_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_70_0 = (mul_((mul_(d, c)), (mul_(d, c))));
	let temp_70_1 = (mul_((mul_(d, c)), (mul_(d, c))));
	assert(eq_(temp_70_0, temp_70_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_71_0 = (sub_((mul_(c, c)), (mul_(c, b))));
	let temp_71_1 = (sub_((mul_(c, c)), (mul_(c, b))));
	assert(eq_(temp_71_0, temp_71_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_72_0 = (mul_((mul_(c, c)), b));
	let temp_72_1 = (mul_((mul_(c, c)), b));
	assert(eq_(temp_72_0, temp_72_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_73_0 = (add_((mul_(b, d)), (mul_(c, b))));
	let temp_73_1 = (add_((mul_(c, b)), (mul_(b, d))));
	assert(eq_(temp_73_0, temp_73_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_74_0 = (add_((mul_(as_elem(70), a)), (mul_(c, d))));
	let temp_74_1 = (add_((mul_(as_elem(70), a)), (mul_(d, c))));
	assert(eq_(temp_74_0, temp_74_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_75_0 = (mul_((mul_((mod_(a, m)), (mod_(as_elem(97), m)))), (mul_(a, d))));
	let temp_75_1 = (mul_((mul_((mod_(as_elem(97), m)), (mod_(a, m)))), (mul_(a, d))));
	assert(eq_(temp_75_0, temp_75_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_76_0 = (sub_((mul_(c, d)), (mul_(c, a))));
	let temp_76_1 = (sub_((mul_(d, c)), (mul_(c, a))));
	assert(eq_(temp_76_0, temp_76_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_77_0 = (add_((mul_(d, (mod_(a, m)))), (mul_((mod_(a, m)), (mod_(d, m))))));
	let temp_77_1 = (add_((mul_((mod_(a, m)), (mod_(d, m)))), (mul_(d, (mod_(a, m))))));
	assert(eq_(temp_77_0, temp_77_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_78_0 = (mod_((mul_((mul_(c, d)), (mod_((mul_(d, c)), m)))), m));
	let temp_78_1 = (mod_((sub_((mul_((mul_(c, d)), (mod_((mul_(d, c)), m)))), (mul_((mul_((mul_(d, d)), (mul_(a, d)))), m)))), m));
	assert(eq_(temp_78_0, temp_78_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_79_0 = (mul_((mul_(d, c)), (mul_(c, (mod_(c, m))))));
	let temp_79_1 = (mul_((mul_(d, c)), (mul_(c, (mod_((add_((mul_((mul_((mul_((mod_(c, m)), a)), (mul_(a, d)))), m)), c)), m))))));
	assert(eq_(temp_79_0, temp_79_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_80_0 = (mul_((sub_(d, d)), (mul_(d, b))));
	let temp_80_1 = (mul_((mul_((sub_(d, d)), d)), b));
	assert(eq_(temp_80_0, temp_80_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_81_0 = (mul_((mul_(a, c)), (mul_(c, a))));
	let temp_81_1 = (mul_((mul_(c, a)), (mul_(c, a))));
	assert(eq_(temp_81_0, temp_81_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_82_0 = (add_((mul_(b, b)), (mul_(b, b))));
	let temp_82_1 = (add_((mul_(b, b)), (mul_(b, b))));
	assert(eq_(temp_82_0, temp_82_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_83_0 = (mul_((mul_((mod_(b, m)), c)), (mod_((mul_(b, b)), m))));
	let temp_83_1 = (mul_((mul_((mod_((add_((mul_((mul_((mod_((sub_(a, c)), m)), (mul_((mod_(c, m)), c)))), m)), b)), m)), c)), (mod_((mul_(b, b)), m))));
	assert(eq_(temp_83_0, temp_83_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_84_0 = (mul_((mul_(a, a)), (mul_(a, a))));
	let temp_84_1 = (mul_((mul_(a, a)), (mul_(a, a))));
	assert(eq_(temp_84_0, temp_84_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_85_0 = (sub_((mul_(b, c)), (mul_(b, (mod_(c, m))))));
	let temp_85_1 = (sub_((mul_(b, c)), (mul_(b, (mod_((add_((mul_((mul_((mul_(d, a)), (mul_(d, d)))), m)), c)), m))))));
	assert(eq_(temp_85_0, temp_85_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_86_0 = (mul_((sub_(c, c)), (mod_((mul_(b, d)), m))));
	let temp_86_1 = (sub_((mul_(c, (mod_((mul_(b, d)), m)))), (mul_(c, (mod_((mul_(b, d)), m))))));
	assert(eq_(temp_86_0, temp_86_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_87_0 = (mul_((mul_(a, (mod_(b, m)))), (sub_(d, d))));
	let temp_87_1 = (mul_((mul_(a, (mod_((add_((mul_((mul_((sub_((mod_(d, m)), a)), (mul_(c, (mod_(c, m)))))), m)), b)), m)))), (sub_(d, d))));
	assert(eq_(temp_87_0, temp_87_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_88_0 = (mul_((mul_(d, a)), (add_(c, d))));
	let temp_88_1 = (mul_((mul_(d, a)), (add_(d, c))));
	assert(eq_(temp_88_0, temp_88_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_89_0 = (mul_((mul_(a, a)), (mul_(c, a))));
	let temp_89_1 = (mul_(a, (mul_(a, (mul_(c, a))))));
	assert(eq_(temp_89_0, temp_89_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_90_0 = (sub_((mul_((mod_(a, m)), c)), (mul_(a, c))));
	let temp_90_1 = (sub_((mul_((mod_(a, m)), c)), (mul_(c, a))));
	assert(eq_(temp_90_0, temp_90_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_91_0 = (mul_((add_(c, a)), (mul_(a, (mod_(b, m))))));
	let temp_91_1 = (add_((mul_(c, (mul_(a, (mod_(b, m)))))), (mul_(a, (mul_(a, (mod_(b, m))))))));
	assert(eq_(temp_91_0, temp_91_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_92_0 = (mul_((mod_((add_(a, b)), m)), (sub_(b, c))));
	let temp_92_1 = (mul_((mod_((add_(a, (mod_(b, m)))), m)), (sub_(b, c))));
	assert(eq_(temp_92_0, temp_92_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_93_0 = (mul_((add_(d, a)), (mul_(c, c))));
	let temp_93_1 = (mul_((mul_((add_(d, a)), c)), c));
	assert(eq_(temp_93_0, temp_93_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_94_0 = (mul_((mod_((mul_((mod_(d, m)), d)), m)), (mul_(d, d))));
	let temp_94_1 = (mul_((mod_((add_((mul_((sub_((mul_(a, c)), (mul_((mod_(d, m)), b)))), m)), (mul_((mod_(d, m)), d)))), m)), (mul_(d, d))));
	assert(eq_(temp_94_0, temp_94_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_95_0 = (mul_((mul_(a, c)), (mul_(a, b))));
	let temp_95_1 = (mul_((mul_(a, b)), (mul_(a, c))));
	assert(eq_(temp_95_0, temp_95_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_96_0 = (sub_((mul_(b, (mod_(d, m)))), (mul_(a, d))));
	let temp_96_1 = (sub_((mul_((mod_(d, m)), b)), (mul_(a, d))));
	assert(eq_(temp_96_0, temp_96_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_97_0 = (mul_((sub_(c, d)), (add_(c, c))));
	let temp_97_1 = (mul_((sub_(c, d)), (add_(c, c))));
	assert(eq_(temp_97_0, temp_97_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_98_0 = (mul_((mul_(d, b)), (mod_((mul_((mod_(b, m)), b)), m))));
	let temp_98_1 = (mul_((mod_((mul_((mod_(b, m)), b)), m)), (mul_(d, b))));
	assert(eq_(temp_98_0, temp_98_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_99_0 = (mod_((mul_((mul_((mod_(d, m)), b)), (add_(d, b)))), m));
	let temp_99_1 = (mod_((mul_((mul_((mod_(d, m)), b)), (add_(b, d)))), m));
	assert(eq_(temp_99_0, temp_99_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_100_0 = (sub_((mul_(b, c)), (mul_(d, a))));
	let temp_100_1 = (sub_((mul_(b, c)), (mul_(a, d))));
	assert(eq_(temp_100_0, temp_100_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_101_0 = (mul_((mul_(a, d)), (mul_(c, a))));
	let temp_101_1 = (mul_((mul_(d, a)), (mul_(c, a))));
	assert(eq_(temp_101_0, temp_101_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_102_0 = (mod_((mul_((mul_(a, a)), (mul_((mod_(c, m)), b)))), m));
	let temp_102_1 = (mod_((mul_((mul_(a, a)), (mul_(b, (mod_(c, m)))))), m));
	assert(eq_(temp_102_0, temp_102_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_103_0 = (mul_((mul_((mod_(a, m)), b)), (mul_(d, d))));
	let temp_103_1 = (mul_((mul_((mul_((mod_(a, m)), b)), d)), d));
	assert(eq_(temp_103_0, temp_103_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_104_0 = (mul_((mod_((mul_(a, a)), m)), (mul_(a, a))));
	let temp_104_1 = (mul_((mod_((mul_(a, a)), m)), (mul_(a, a))));
	assert(eq_(temp_104_0, temp_104_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_105_0 = (mod_((sub_((mul_(c, a)), (mul_(d, c)))), m));
	let temp_105_1 = (mod_((sub_((mul_(a, c)), (mul_(d, c)))), m));
	assert(eq_(temp_105_0, temp_105_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_106_0 = (sub_((mul_(a, d)), (mul_(b, a))));
	let temp_106_1 = (sub_((mul_(d, a)), (mul_(b, a))));
	assert(eq_(temp_106_0, temp_106_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_107_0 = (mul_((sub_(c, c)), (mod_((mul_((mod_(d, m)), a)), m))));
	let temp_107_1 = (sub_((mul_(c, (mod_((mul_((mod_(d, m)), a)), m)))), (mul_(c, (mod_((mul_((mod_(d, m)), a)), m))))));
	assert(eq_(temp_107_0, temp_107_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_108_0 = (add_((mul_(a, a)), (mod_((mul_(c, c)), m))));
	let temp_108_1 = (add_((mul_(a, a)), (mod_((sub_((mul_(c, c)), (mul_((mul_((mul_((mod_(b, m)), b)), (add_(c, (mod_(c, m)))))), m)))), m))));
	assert(eq_(temp_108_0, temp_108_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_109_0 = (mul_((mul_((mod_(b, m)), d)), (mul_(d, c))));
	let temp_109_1 = (mul_((mul_((mod_((add_((mul_((mul_((mul_(d, a)), (mul_(c, d)))), m)), b)), m)), d)), (mul_(d, c))));
	assert(eq_(temp_109_0, temp_109_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_110_0 = (mul_((mul_(d, a)), (mul_(d, (mod_(d, m))))));
	let temp_110_1 = (mul_((mul_(d, a)), (mul_((mod_(d, m)), d))));
	assert(eq_(temp_110_0, temp_110_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_111_0 = (mod_((mul_((mul_(b, c)), (mod_((mul_(as_elem(56), a)), m)))), m));
	let temp_111_1 = (mod_((add_((mul_((mul_(b, c)), (mod_((mul_(as_elem(56), a)), m)))), (mul_((mul_((mul_(a, d)), (mul_(b, as_elem(46))))), m)))), m));
	assert(eq_(temp_111_0, temp_111_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_112_0 = (add_((add_(a, a)), (mul_(c, c))));
	let temp_112_1 = (add_((mul_(c, c)), (add_(a, a))));
	assert(eq_(temp_112_0, temp_112_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_113_0 = (mul_((mul_(d, (mod_(b, m)))), (mul_(c, b))));
	let temp_113_1 = (mul_((mul_((mod_(b, m)), d)), (mul_(c, b))));
	assert(eq_(temp_113_0, temp_113_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_114_0 = (mul_((add_(c, a)), (mul_(a, d))));
	let temp_114_1 = (mul_((add_(a, c)), (mul_(a, d))));
	assert(eq_(temp_114_0, temp_114_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_115_0 = (mul_((mul_(c, a)), (add_(c, a))));
	let temp_115_1 = (mul_(c, (mul_(a, (add_(c, a))))));
	assert(eq_(temp_115_0, temp_115_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_116_0 = (mod_((mul_((mul_(b, b)), (mul_(a, d)))), m));
	let temp_116_1 = (mod_((mul_(b, (mul_(b, (mul_(a, d)))))), m));
	assert(eq_(temp_116_0, temp_116_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_117_0 = (sub_((mul_(c, d)), (mul_(a, d))));
	let temp_117_1 = (mul_((sub_(c, a)), d));
	assert(eq_(temp_117_0, temp_117_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_118_0 = (mul_((mul_(b, b)), (mul_(c, b))));
	let temp_118_1 = (mul_((mul_((mul_(b, b)), c)), b));
	assert(eq_(temp_118_0, temp_118_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_119_0 = (mul_((mul_(a, c)), (mul_((mod_(a, m)), d))));
	let temp_119_1 = (mul_((mul_(a, c)), (mul_((mod_((add_((mul_((mul_((mul_(b, b)), (mod_((mul_(c, a)), m)))), m)), a)), m)), d))));
	assert(eq_(temp_119_0, temp_119_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_120_0 = (mul_((mul_(a, d)), (mul_(a, c))));
	let temp_120_1 = (mul_((mul_(d, a)), (mul_(a, c))));
	assert(eq_(temp_120_0, temp_120_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_121_0 = (mul_((mod_((mul_(d, d)), m)), (mul_(c, c))));
	let temp_121_1 = (mul_((mul_((mod_((mul_(d, d)), m)), c)), c));
	assert(eq_(temp_121_0, temp_121_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_122_0 = (mul_((mod_((mul_((mod_(b, m)), b)), m)), (mul_(b, a))));
	let temp_122_1 = (mul_((mul_((mod_((mul_((mod_(b, m)), b)), m)), b)), a));
	assert(eq_(temp_122_0, temp_122_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_123_0 = (mul_((mul_(a, b)), (sub_(d, a))));
	let temp_123_1 = (mul_(a, (mul_(b, (sub_(d, a))))));
	assert(eq_(temp_123_0, temp_123_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_124_0 = (mul_((mul_(d, c)), (mul_(a, b))));
	let temp_124_1 = (mul_((mul_(c, d)), (mul_(a, b))));
	assert(eq_(temp_124_0, temp_124_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_125_0 = (mul_((mul_((mod_(a, m)), c)), c));
	let temp_125_1 = (mul_((mod_(a, m)), (mul_(c, c))));
	assert(eq_(temp_125_0, temp_125_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_126_0 = (mod_((mul_((sub_(d, a)), (mod_((mul_(a, (mod_(a, m)))), m)))), m));
	let temp_126_1 = (mod_((mul_((sub_(d, a)), (mod_((mod_((mul_(a, a)), m)), m)))), m));
	assert(eq_(temp_126_0, temp_126_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_127_0 = (mul_((mul_(a, c)), (add_(c, c))));
	let temp_127_1 = (mul_((mul_(a, c)), (add_(c, c))));
	assert(eq_(temp_127_0, temp_127_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_128_0 = (mod_((add_((mul_(b, (mod_(a, m)))), (mul_(a, c)))), m));
	let temp_128_1 = (mod_((add_((mul_((mul_((mul_(c, b)), (mul_(c, (mod_(c, m)))))), m)), (add_((mul_(b, (mod_(a, m)))), (mul_(a, c)))))), m));
	assert(eq_(temp_128_0, temp_128_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_129_0 = (mul_((add_(b, d)), (mul_(a, b))));
	let temp_129_1 = (mul_((mul_(a, b)), (add_(b, d))));
	assert(eq_(temp_129_0, temp_129_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_130_0 = (mul_((mul_(a, d)), (mul_(b, a))));
	let temp_130_1 = (mul_((mul_((mul_(a, d)), b)), a));
	assert(eq_(temp_130_0, temp_130_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_131_0 = (mul_((mul_(b, a)), (mul_(b, d))));
	let temp_131_1 = (mul_(b, (mul_(a, (mul_(b, d))))));
	assert(eq_(temp_131_0, temp_131_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_132_0 = (mul_((mul_(as_elem(73), a)), b));
	let temp_132_1 = (mul_(as_elem(73), (mul_(a, b))));
	assert(eq_(temp_132_0, temp_132_1)) by 
			{lemma_mul_properties_auto_1();}// 1

}

} // verus!