use builtin_macros::*;
// use builtin::*;
mod nl_basics;
use crate::nl_basics::*;
verus! {

pub proof fn auto_0(a: Elem, b: Elem, c: Elem, d: Elem, m: Elem)
{
	let temp_0_0 = (mod_((mul_((mul_(b, c)), (mul_(c, a)))), m));
	let temp_0_1 = (mod_((add_((mul_((mul_(b, c)), (mul_(c, a)))), (mul_((mul_((mul_(b, d)), (mul_(c, d)))), m)))), m));
	assert(eq_(temp_0_0, temp_0_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_1_0 = (sub_((mul_(b, a)), (mul_(a, a))));
	let temp_1_1 = (mul_((sub_(b, a)), a));
	assert(eq_(temp_1_0, temp_1_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_2_0 = (sub_((mod_((mul_(as_elem(30), d)), m)), (mul_(b, d))));
	let temp_2_1 = (sub_((mod_((add_((mul_((mul_((mul_(d, c)), (mul_(as_elem(95), a)))), m)), (mul_(as_elem(30), d)))), m)), (mul_(b, d))));
	assert(eq_(temp_2_0, temp_2_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_3_0 = (mod_((mul_((mul_(d, d)), (mul_(d, c)))), m));
	let temp_3_1 = (mod_((mul_((mul_(d, c)), (mul_(d, d)))), m));
	assert(eq_(temp_3_0, temp_3_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_4_0 = (mul_((add_(a, d)), (mul_(a, d))));
	let temp_4_1 = (mul_((mul_((add_(a, d)), a)), d));
	assert(eq_(temp_4_0, temp_4_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_5_0 = (mul_((mul_(a, (mod_(c, m)))), (mul_(a, (mod_(a, m))))));
	let temp_5_1 = (mul_(a, (mul_((mod_(c, m)), (mul_(a, (mod_(a, m))))))));
	assert(eq_(temp_5_0, temp_5_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_6_0 = (mul_((mul_(c, c)), (mul_(c, a))));
	let temp_6_1 = (mul_(c, (mul_(c, (mul_(c, a))))));
	assert(eq_(temp_6_0, temp_6_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_7_0 = (mul_((mul_((mod_(c, m)), (mod_(b, m)))), (mul_(a, b))));
	let temp_7_1 = (mul_((mul_((mod_((add_((mul_((sub_((mul_(b, a)), (mul_(b, b)))), m)), c)), m)), (mod_(b, m)))), (mul_(a, b))));
	assert(eq_(temp_7_0, temp_7_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_8_0 = (mul_((sub_(d, a)), (mul_(a, d))));
	let temp_8_1 = (sub_((mul_(d, (mul_(a, d)))), (mul_(a, (mul_(a, d))))));
	assert(eq_(temp_8_0, temp_8_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_9_0 = (sub_((mul_((mod_(b, m)), a)), (mul_(a, b))));
	let temp_9_1 = (sub_((mul_(a, (mod_(b, m)))), (mul_(a, b))));
	assert(eq_(temp_9_0, temp_9_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_10_0 = (mul_((mul_(d, a)), (mul_(a, a))));
	let temp_10_1 = (mul_((mul_(d, a)), (mul_(a, a))));
	assert(eq_(temp_10_0, temp_10_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_11_0 = (mul_((mul_(b, c)), (mul_(b, (mod_(b, m))))));
	let temp_11_1 = (mul_((mul_(c, b)), (mul_(b, (mod_(b, m))))));
	assert(eq_(temp_11_0, temp_11_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_12_0 = (mul_((mul_(a, c)), (add_(b, (mod_(c, m))))));
	let temp_12_1 = (add_((mul_((mul_(a, c)), b)), (mul_((mul_(a, c)), (mod_(c, m))))));
	assert(eq_(temp_12_0, temp_12_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_13_0 = (mul_((mul_(b, d)), (mul_(c, b))));
	let temp_13_1 = (mul_((mul_(d, b)), (mul_(c, b))));
	assert(eq_(temp_13_0, temp_13_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_14_0 = (mul_((mul_(c, b)), (mul_(a, c))));
	let temp_14_1 = (mul_((mul_(c, b)), (mul_(c, a))));
	assert(eq_(temp_14_0, temp_14_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_15_0 = (mul_((mod_((add_(c, as_elem(76))), m)), (mul_(b, b))));
	let temp_15_1 = (mul_((mod_((add_(as_elem(76), c)), m)), (mul_(b, b))));
	assert(eq_(temp_15_0, temp_15_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_16_0 = (sub_((mul_(a, c)), (mul_(a, c))));
	let temp_16_1 = (sub_((mul_(a, c)), (mul_(c, a))));
	assert(eq_(temp_16_0, temp_16_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_17_0 = (sub_((sub_(c, (mod_(c, m)))), (mod_((mul_(a, d)), m))));
	let temp_17_1 = (sub_((sub_(c, (mod_(c, m)))), (mod_((mul_(d, a)), m))));
	assert(eq_(temp_17_0, temp_17_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_18_0 = (mul_((mul_(b, c)), (mul_(b, (mod_(a, m))))));
	let temp_18_1 = (mul_(b, (mul_(c, (mul_(b, (mod_(a, m))))))));
	assert(eq_(temp_18_0, temp_18_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_19_0 = (mod_((mul_((mul_((mod_(a, m)), a)), (mul_(b, (mod_(d, m)))))), m));
	let temp_19_1 = (mod_((mul_((mul_((mod_(a, m)), a)), (mul_(b, (mod_((sub_(d, (mul_((mul_((mul_(c, a)), (mul_(d, a)))), m)))), m)))))), m));
	assert(eq_(temp_19_0, temp_19_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_20_0 = (mul_((mul_(a, b)), (add_(a, d))));
	let temp_20_1 = (mul_(a, (mul_(b, (add_(a, d))))));
	assert(eq_(temp_20_0, temp_20_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_21_0 = (mul_((mul_(b, (mod_(a, m)))), (mod_((sub_((mod_(d, m)), d)), m))));
	let temp_21_1 = (mul_((mul_(b, (mod_(a, m)))), (mod_((add_((mul_((mul_((mul_(c, a)), (sub_(a, b)))), m)), (sub_((mod_(d, m)), d)))), m))));
	assert(eq_(temp_21_0, temp_21_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_22_0 = (add_((mul_(c, a)), (mod_((mul_((mod_(d, m)), b)), m))));
	let temp_22_1 = (add_((mul_(a, c)), (mod_((mul_((mod_(d, m)), b)), m))));
	assert(eq_(temp_22_0, temp_22_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_23_0 = (mul_((mul_((mod_(a, m)), b)), (mul_(a, b))));
	let temp_23_1 = (mul_((mul_((mod_((add_(a, (mul_((mul_((mul_(a, a)), (sub_(a, a)))), m)))), m)), b)), (mul_(a, b))));
	assert(eq_(temp_23_0, temp_23_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_24_0 = (mul_((mul_(a, b)), (mul_(a, b))));
	let temp_24_1 = (mul_(a, (mul_(b, (mul_(a, b))))));
	assert(eq_(temp_24_0, temp_24_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_25_0 = (mul_((mul_(d, a)), (mul_(b, c))));
	let temp_25_1 = (mul_((mul_((mul_(d, a)), b)), c));
	assert(eq_(temp_25_0, temp_25_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_26_0 = (add_((mul_(b, b)), (mod_((sub_((mod_(c, m)), b)), m))));
	let temp_26_1 = (add_((mul_(b, b)), (mod_((sub_((mod_((mod_(c, m)), m)), b)), m))));
	assert(eq_(temp_26_0, temp_26_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_27_0 = (mul_((mul_(c, c)), (mod_((mul_(b, c)), m))));
	let temp_27_1 = (mul_((mul_(c, c)), (mod_((add_((mul_((mul_((sub_(d, c)), (add_(b, b)))), m)), (mul_(b, c)))), m))));
	assert(eq_(temp_27_0, temp_27_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_28_0 = (sub_((mul_(a, b)), (add_((mod_(a, m)), d))));
	let temp_28_1 = (sub_((mul_(b, a)), (add_((mod_(a, m)), d))));
	assert(eq_(temp_28_0, temp_28_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_29_0 = (sub_((mul_(a, c)), (mul_(d, b))));
	let temp_29_1 = (sub_((mul_(a, c)), (mul_(b, d))));
	assert(eq_(temp_29_0, temp_29_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_30_0 = (mul_((mul_((mod_(c, m)), d)), (mod_((mul_(b, d)), m))));
	let temp_30_1 = (mul_((mul_((mod_((add_((mul_((mul_((mul_(a, a)), (mul_(d, b)))), m)), c)), m)), d)), (mod_((mul_(b, d)), m))));
	assert(eq_(temp_30_0, temp_30_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_31_0 = (mul_((mul_(d, c)), (sub_(d, b))));
	let temp_31_1 = (mul_(d, (mul_(c, (sub_(d, b))))));
	assert(eq_(temp_31_0, temp_31_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_32_0 = (mul_((mul_((mod_(c, m)), a)), (mul_((mod_(a, m)), d))));
	let temp_32_1 = (mul_((mul_((mul_((mod_(c, m)), a)), (mod_(a, m)))), d));
	assert(eq_(temp_32_0, temp_32_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_33_0 = (mul_((mul_(a, c)), (mul_(c, (mod_(b, m))))));
	let temp_33_1 = (mul_(a, (mul_(c, (mul_(c, (mod_(b, m))))))));
	assert(eq_(temp_33_0, temp_33_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_34_0 = (mul_((mul_(c, (mod_(d, m)))), (mul_(a, d))));
	let temp_34_1 = (mul_((mul_(c, (mod_((add_((mul_((mul_((mul_((mod_(b, m)), a)), (sub_(c, (mod_(c, m)))))), m)), d)), m)))), (mul_(a, d))));
	assert(eq_(temp_34_0, temp_34_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_35_0 = (mul_((mul_(b, (mod_(c, m)))), (sub_(d, a))));
	let temp_35_1 = (mul_(b, (mul_((mod_(c, m)), (sub_(d, a))))));
	assert(eq_(temp_35_0, temp_35_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_36_0 = (mul_((mul_(d, a)), (mul_(c, a))));
	let temp_36_1 = (mul_((mul_(d, a)), (mul_(a, c))));
	assert(eq_(temp_36_0, temp_36_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_37_0 = (mul_((sub_(a, c)), (mod_((mul_((mod_(b, m)), d)), m))));
	let temp_37_1 = (sub_((mul_(a, (mod_((mul_((mod_(b, m)), d)), m)))), (mul_(c, (mod_((mul_((mod_(b, m)), d)), m))))));
	assert(eq_(temp_37_0, temp_37_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_38_0 = (mul_((mod_((mul_(d, a)), m)), (add_(c, b))));
	let temp_38_1 = (mul_((mod_((add_((mul_((mul_((mul_(a, b)), (mul_(a, c)))), m)), (mul_(d, a)))), m)), (add_(c, b))));
	assert(eq_(temp_38_0, temp_38_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_39_0 = (mul_((mul_(a, c)), (add_(a, a))));
	let temp_39_1 = (mul_((mul_(a, c)), (add_(a, a))));
	assert(eq_(temp_39_0, temp_39_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_40_0 = (mod_((mul_((mul_(b, b)), (mul_(b, c)))), m));
	let temp_40_1 = (mod_((mul_((mul_(b, c)), (mul_(b, b)))), m));
	assert(eq_(temp_40_0, temp_40_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_41_0 = (mod_((mul_((sub_(b, c)), (mod_((mul_((mod_(d, m)), b)), m)))), m));
	let temp_41_1 = (mod_((sub_((mul_(b, (mod_((mul_((mod_(d, m)), b)), m)))), (mul_(c, (mod_((mul_((mod_(d, m)), b)), m)))))), m));
	assert(eq_(temp_41_0, temp_41_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_42_0 = (mod_((mul_((mod_((add_(b, b)), m)), (add_(b, b)))), m));
	let temp_42_1 = (mod_((mul_((mod_((add_((add_(b, b)), (mul_((mul_((mul_(c, d)), (mul_(b, c)))), m)))), m)), (add_(b, b)))), m));
	assert(eq_(temp_42_0, temp_42_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_43_0 = (sub_((mul_(c, c)), (mod_((mul_(c, d)), m))));
	let temp_43_1 = (sub_((mul_(c, c)), (mod_((mul_(d, c)), m))));
	assert(eq_(temp_43_0, temp_43_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_44_0 = (sub_((mul_((mod_(a, m)), c)), (mul_(b, a))));
	let temp_44_1 = (sub_((mul_((mod_((add_((mul_((mul_((mul_(c, a)), (mod_((add_(c, a)), m)))), m)), a)), m)), c)), (mul_(b, a))));
	assert(eq_(temp_44_0, temp_44_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_45_0 = (mul_((mul_(as_elem(62), c)), (mul_(d, b))));
	let temp_45_1 = (mul_((mul_(d, b)), (mul_(as_elem(62), c))));
	assert(eq_(temp_45_0, temp_45_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_46_0 = (mul_((mul_(b, a)), (mul_(d, a))));
	let temp_46_1 = (mul_((mul_((mul_(b, a)), d)), a));
	assert(eq_(temp_46_0, temp_46_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_47_0 = (mul_((mul_(a, b)), (mul_(a, a))));
	let temp_47_1 = (mul_(a, (mul_(b, (mul_(a, a))))));
	assert(eq_(temp_47_0, temp_47_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_48_0 = (add_((mul_(b, b)), (mul_(b, b))));
	let temp_48_1 = (add_((mul_(b, b)), (mul_(b, b))));
	assert(eq_(temp_48_0, temp_48_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_49_0 = (mul_((mul_(a, (mod_(a, m)))), (mul_(d, a))));
	let temp_49_1 = (mul_(a, (mul_((mod_(a, m)), (mul_(d, a))))));
	assert(eq_(temp_49_0, temp_49_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_50_0 = (mul_((mul_(as_elem(69), d)), (mod_((mul_(a, a)), m))));
	let temp_50_1 = (mul_(as_elem(69), (mul_(d, (mod_((mul_(a, a)), m))))));
	assert(eq_(temp_50_0, temp_50_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_51_0 = (mul_((mul_(b, d)), (mul_(as_elem(97), a))));
	let temp_51_1 = (mul_((mul_(d, b)), (mul_(as_elem(97), a))));
	assert(eq_(temp_51_0, temp_51_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_52_0 = (mul_((mul_(c, a)), (mod_((mul_(b, d)), m))));
	let temp_52_1 = (mul_((mod_((mul_(b, d)), m)), (mul_(c, a))));
	assert(eq_(temp_52_0, temp_52_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_53_0 = (mul_((mul_(b, d)), (add_(d, a))));
	let temp_53_1 = (mul_((mul_(b, d)), (add_(a, d))));
	assert(eq_(temp_53_0, temp_53_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_54_0 = (mul_((mul_(a, c)), (mul_(a, a))));
	let temp_54_1 = (mul_((mul_(a, a)), (mul_(a, c))));
	assert(eq_(temp_54_0, temp_54_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_55_0 = (mod_((mul_((mul_(d, (mod_(b, m)))), (mul_(d, (mod_(a, m)))))), m));
	let temp_55_1 = (mod_((add_((mul_((mul_((mul_(d, a)), (mul_(d, b)))), m)), (mul_((mul_(d, (mod_(b, m)))), (mul_(d, (mod_(a, m)))))))), m));
	assert(eq_(temp_55_0, temp_55_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_56_0 = (mul_((mod_((add_(d, c)), m)), (add_(d, a))));
	let temp_56_1 = (add_((mul_((mod_((add_(d, c)), m)), d)), (mul_((mod_((add_(d, c)), m)), a))));
	assert(eq_(temp_56_0, temp_56_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_57_0 = (mul_((mul_(d, c)), (mul_(c, d))));
	let temp_57_1 = (mul_((mul_(c, d)), (mul_(d, c))));
	assert(eq_(temp_57_0, temp_57_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_58_0 = (mul_((sub_(a, a)), (mul_(b, as_elem(6)))));
	let temp_58_1 = (mul_((sub_(a, a)), (mul_(as_elem(6), b))));
	assert(eq_(temp_58_0, temp_58_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_59_0 = (mul_((mul_(c, (mod_(a, m)))), (mul_(d, a))));
	let temp_59_1 = (mul_((mul_((mul_(c, (mod_(a, m)))), d)), a));
	assert(eq_(temp_59_0, temp_59_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_60_0 = (mul_((mul_(b, a)), (mul_(a, b))));
	let temp_60_1 = (mul_((mul_(a, b)), (mul_(b, a))));
	assert(eq_(temp_60_0, temp_60_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_61_0 = (mul_((mul_(d, a)), b));
	let temp_61_1 = (mul_(b, (mul_(d, a))));
	assert(eq_(temp_61_0, temp_61_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_62_0 = (mul_((mul_(a, a)), (mul_(c, c))));
	let temp_62_1 = (mul_((mul_(a, a)), (mul_(c, c))));
	assert(eq_(temp_62_0, temp_62_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_63_0 = (mul_((mul_(c, a)), (mul_(b, (mod_(c, m))))));
	let temp_63_1 = (mul_((mul_(c, a)), (mul_(b, (mod_((add_((mul_((mul_((mul_(c, a)), (mul_(d, c)))), m)), c)), m))))));
	assert(eq_(temp_63_0, temp_63_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_64_0 = (mul_((mod_((mul_(d, (mod_(c, m)))), m)), (mul_(a, d))));
	let temp_64_1 = (mul_((mod_((mul_(d, (mod_(c, m)))), m)), (mul_(d, a))));
	assert(eq_(temp_64_0, temp_64_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_65_0 = (mul_((mul_(a, b)), (mul_(d, d))));
	let temp_65_1 = (mul_((mul_((mul_(a, b)), d)), d));
	assert(eq_(temp_65_0, temp_65_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_66_0 = (mul_((mul_((mod_(d, m)), c)), (mul_(a, b))));
	let temp_66_1 = (mul_((mul_((mul_((mod_(d, m)), c)), a)), b));
	assert(eq_(temp_66_0, temp_66_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_67_0 = (add_((mod_((mul_(d, b)), m)), (mul_(b, b))));
	let temp_67_1 = (add_((mul_(b, b)), (mod_((mul_(d, b)), m))));
	assert(eq_(temp_67_0, temp_67_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_68_0 = (mul_((mul_(d, d)), (mul_(a, c))));
	let temp_68_1 = (mul_((mul_(d, d)), (mul_(c, a))));
	assert(eq_(temp_68_0, temp_68_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_69_0 = (mul_((mul_(d, c)), (mul_(a, a))));
	let temp_69_1 = (mul_((mul_((mul_(d, c)), a)), a));
	assert(eq_(temp_69_0, temp_69_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_70_0 = (mul_((mul_(b, a)), (mul_(b, d))));
	let temp_70_1 = (mul_((mul_(b, a)), (mul_(d, b))));
	assert(eq_(temp_70_0, temp_70_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_71_0 = (mul_((mul_(d, (mod_(b, m)))), (mul_(a, b))));
	let temp_71_1 = (mul_(d, (mul_((mod_(b, m)), (mul_(a, b))))));
	assert(eq_(temp_71_0, temp_71_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_72_0 = (mul_((mul_(b, b)), (mul_(c, d))));
	let temp_72_1 = (mul_(b, (mul_(b, (mul_(c, d))))));
	assert(eq_(temp_72_0, temp_72_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_73_0 = (mod_((mul_(b, (mul_(as_elem(49), a)))), m));
	let temp_73_1 = (mod_((add_((mul_((mul_((mul_(d, (mod_(a, m)))), a)), m)), (mul_(b, (mul_(as_elem(49), a)))))), m));
	assert(eq_(temp_73_0, temp_73_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_74_0 = (mul_((sub_(a, d)), (mul_(b, b))));
	let temp_74_1 = (mul_((sub_(a, d)), (mul_(b, b))));
	assert(eq_(temp_74_0, temp_74_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_75_0 = (mul_((sub_(a, d)), (mul_(a, d))));
	let temp_75_1 = (mul_((mul_((sub_(a, d)), a)), d));
	assert(eq_(temp_75_0, temp_75_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_76_0 = (mod_((mul_((mul_(b, as_elem(12))), (sub_(d, b)))), m));
	let temp_76_1 = (mod_((add_((mul_((mul_(b, as_elem(12))), (sub_(d, b)))), (mul_((add_((mul_(a, b)), (mul_(a, (mod_(c, m)))))), m)))), m));
	assert(eq_(temp_76_0, temp_76_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_77_0 = (mul_((mul_((mod_(d, m)), b)), (mul_(d, d))));
	let temp_77_1 = (mul_((mul_((mod_((add_(d, (mul_((add_((mul_((mod_(d, m)), b)), (mod_((mul_(c, b)), m)))), m)))), m)), b)), (mul_(d, d))));
	assert(eq_(temp_77_0, temp_77_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_78_0 = (mul_((mod_((add_(c, c)), m)), (mul_(b, (mod_(a, m))))));
	let temp_78_1 = (mul_((mod_((add_(c, c)), m)), (mul_((mod_(a, m)), b))));
	assert(eq_(temp_78_0, temp_78_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_79_0 = (mul_((mul_(a, a)), c));
	let temp_79_1 = (mul_(c, (mul_(a, a))));
	assert(eq_(temp_79_0, temp_79_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_80_0 = (sub_((mul_(d, b)), (add_(b, a))));
	let temp_80_1 = (sub_((mul_(b, d)), (add_(b, a))));
	assert(eq_(temp_80_0, temp_80_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_81_0 = (mul_((add_(c, d)), (mod_((mul_(a, a)), m))));
	let temp_81_1 = (mul_((add_(d, c)), (mod_((mul_(a, a)), m))));
	assert(eq_(temp_81_0, temp_81_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_82_0 = (add_((mul_(a, (mod_(b, m)))), (mul_(as_elem(62), a))));
	let temp_82_1 = (add_((mul_(a, (mod_((add_(b, (mul_((mul_((mul_(a, d)), (mul_(b, d)))), m)))), m)))), (mul_(as_elem(62), a))));
	assert(eq_(temp_82_0, temp_82_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_83_0 = (mul_((sub_(a, d)), (sub_(c, d))));
	let temp_83_1 = (mul_((sub_(c, d)), (sub_(a, d))));
	assert(eq_(temp_83_0, temp_83_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_84_0 = (mul_((mul_(d, a)), (mul_(c, c))));
	let temp_84_1 = (mul_(d, (mul_(a, (mul_(c, c))))));
	assert(eq_(temp_84_0, temp_84_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_85_0 = (mul_((mul_(b, a)), (mul_(d, a))));
	let temp_85_1 = (mul_((mul_(a, b)), (mul_(d, a))));
	assert(eq_(temp_85_0, temp_85_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_86_0 = (mul_((mul_(d, (mod_(a, m)))), (mul_(b, c))));
	let temp_86_1 = (mul_((mul_(d, (mod_((add_(a, (mul_((mul_((mul_(b, c)), (mul_(d, a)))), m)))), m)))), (mul_(b, c))));
	assert(eq_(temp_86_0, temp_86_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_87_0 = (mul_((mul_(a, b)), (add_(c, a))));
	let temp_87_1 = (mul_(a, (mul_(b, (add_(c, a))))));
	assert(eq_(temp_87_0, temp_87_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_88_0 = (mul_((mul_(a, (mod_(c, m)))), (add_(a, d))));
	let temp_88_1 = (mul_((mul_(a, (mod_(c, m)))), (add_(d, a))));
	assert(eq_(temp_88_0, temp_88_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_89_0 = (mul_((mul_(b, a)), (mul_(d, c))));
	let temp_89_1 = (mul_((mul_((mul_(b, a)), d)), c));
	assert(eq_(temp_89_0, temp_89_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_90_0 = (mod_((mul_((mul_(b, c)), (mul_(b, a)))), m));
	let temp_90_1 = (mod_((sub_((mul_((mul_(b, c)), (mul_(b, a)))), (mul_((mul_((sub_(c, b)), (mul_(d, d)))), m)))), m));
	assert(eq_(temp_90_0, temp_90_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_91_0 = (mul_((mul_(b, c)), (mul_(c, (mod_(b, m))))));
	let temp_91_1 = (mul_((mul_(c, b)), (mul_(c, (mod_(b, m))))));
	assert(eq_(temp_91_0, temp_91_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_92_0 = (mul_(a, (mul_(a, c))));
	let temp_92_1 = (mul_(a, (mul_(c, a))));
	assert(eq_(temp_92_0, temp_92_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_93_0 = (add_((sub_(b, (mod_(c, m)))), (mul_(d, (mod_(b, m))))));
	let temp_93_1 = (add_((sub_(b, (mod_((add_((mul_((mul_((mul_(d, c)), (mul_(a, b)))), m)), c)), m)))), (mul_(d, (mod_(b, m))))));
	assert(eq_(temp_93_0, temp_93_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_94_0 = (mul_((mul_(d, c)), (mul_((mod_(c, m)), c))));
	let temp_94_1 = (mul_((mul_(c, d)), (mul_((mod_(c, m)), c))));
	assert(eq_(temp_94_0, temp_94_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_95_0 = (mul_((mul_(b, (mod_(d, m)))), (mul_(d, (mod_(a, m))))));
	let temp_95_1 = (mul_(b, (mul_((mod_(d, m)), (mul_(d, (mod_(a, m))))))));
	assert(eq_(temp_95_0, temp_95_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_96_0 = (mul_((mul_(a, a)), (sub_(d, c))));
	let temp_96_1 = (mul_((mul_(a, a)), (sub_(d, c))));
	assert(eq_(temp_96_0, temp_96_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_97_0 = (mod_((mul_((mul_(d, b)), (mul_(d, (mod_(a, m)))))), m));
	let temp_97_1 = (mod_((mul_((mul_(d, b)), (mul_(d, (mod_((sub_(a, (mul_((mul_((mul_(c, c)), (mod_((sub_(b, d)), m)))), m)))), m)))))), m));
	assert(eq_(temp_97_0, temp_97_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_98_0 = (mul_((mul_(d, d)), (mul_((mod_(a, m)), b))));
	let temp_98_1 = (mul_((mul_(d, d)), (mul_((mod_((add_(a, (mul_((mul_((sub_(b, b)), (mul_((mod_(b, m)), a)))), m)))), m)), b))));
	assert(eq_(temp_98_0, temp_98_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_99_0 = (mul_((mul_(d, d)), (mul_((mod_(b, m)), d))));
	let temp_99_1 = (mul_(d, (mul_(d, (mul_((mod_(b, m)), d))))));
	assert(eq_(temp_99_0, temp_99_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_100_0 = (add_((mul_(b, a)), d));
	let temp_100_1 = (add_(d, (mul_(b, a))));
	assert(eq_(temp_100_0, temp_100_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_101_0 = (sub_((mul_(b, d)), (mul_(b, d))));
	let temp_101_1 = (sub_((mul_(b, d)), (mul_(d, b))));
	assert(eq_(temp_101_0, temp_101_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_102_0 = (mul_((mul_((mod_(c, m)), b)), (mul_(as_elem(64), a))));
	let temp_102_1 = (mul_((mod_(c, m)), (mul_(b, (mul_(as_elem(64), a))))));
	assert(eq_(temp_102_0, temp_102_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_103_0 = (mul_((mul_(c, b)), (mul_((mod_(a, m)), a))));
	let temp_103_1 = (mul_((mul_((mul_(c, b)), (mod_(a, m)))), a));
	assert(eq_(temp_103_0, temp_103_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_104_0 = (mul_((mul_((mod_(a, m)), b)), (add_((mod_(a, m)), (mod_(b, m))))));
	let temp_104_1 = (mul_((mod_(a, m)), (mul_(b, (add_((mod_(a, m)), (mod_(b, m))))))));
	assert(eq_(temp_104_0, temp_104_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_105_0 = (mul_((mul_(b, (mod_(as_elem(31), m)))), (mod_((mul_((mod_(a, m)), (mod_(a, m)))), m))));
	let temp_105_1 = (mul_((mul_(b, (mod_(as_elem(31), m)))), (mod_((add_((mul_((mod_(a, m)), (mod_(a, m)))), (mul_((mul_((mul_(b, a)), (mul_(d, (mod_(a, m)))))), m)))), m))));
	assert(eq_(temp_105_0, temp_105_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_106_0 = (mul_((mul_(b, b)), (mul_(d, d))));
	let temp_106_1 = (mul_(b, (mul_(b, (mul_(d, d))))));
	assert(eq_(temp_106_0, temp_106_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_107_0 = (mul_((mul_(c, b)), (sub_(d, as_elem(69)))));
	let temp_107_1 = (mul_((mul_(b, c)), (sub_(d, as_elem(69)))));
	assert(eq_(temp_107_0, temp_107_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_108_0 = (mod_((mul_((mul_(d, d)), (mul_(d, d)))), m));
	let temp_108_1 = (mod_((mul_((mul_(d, d)), (mul_(d, d)))), m));
	assert(eq_(temp_108_0, temp_108_1)) by 
			{lemma_mul_properties_auto_1();}// 1
	let temp_109_0 = (mul_((mul_((mod_(c, m)), d)), (add_(b, b))));
	let temp_109_1 = (mul_((mul_((mod_(c, m)), d)), (add_(b, b))));
	assert(eq_(temp_109_0, temp_109_1)) by 
			{lemma_mul_properties_auto_1();}// 1

}

} // verus!