(set-option :auto_config false)
(set-option :smt.mbqi false)
(set-option :smt.case_split 3)
(set-option :smt.qi.eager_threshold 100.0)
(set-option :smt.delay_units true)
(set-option :smt.arith.solver 2)
(set-option :smt.arith.nl false)
(set-info :comment ";; Prelude")
(set-info :comment ";; AIR prelude")
(declare-sort %%Function%% 0)
(declare-sort FuelId 0)
(declare-sort Fuel 0)
(declare-const zero Fuel)
(declare-fun succ (Fuel) Fuel)
(declare-fun fuel_bool (FuelId) Bool)
(declare-fun fuel_bool_default (FuelId) Bool)
(declare-const fuel_defaults Bool)
(assert (=> fuel_defaults (forall ((id FuelId)) (! (= (fuel_bool id) (fuel_bool_default id)) :pattern ((fuel_bool id)) :qid prelude_fuel_defaults :skolemid skolem_prelude_fuel_defaults))))
(declare-sort Char 0)
(declare-fun char%from_unicode (Int) Char)
(declare-fun char%to_unicode (Char) Int)
(declare-sort StrSlice 0)
(declare-fun str%strslice_is_ascii (StrSlice) Bool)
(declare-fun str%strslice_len (StrSlice) Int)
(declare-fun str%strslice_get_char (StrSlice Int) Char)
(declare-fun str%new_strlit (Int) StrSlice)
(declare-fun str%from_strlit (StrSlice) Int)
(declare-sort Poly 0)
(declare-sort Height 0)
(declare-fun I (Int) Poly)
(declare-fun B (Bool) Poly)
(declare-fun %I (Poly) Int)
(declare-fun %B (Poly) Bool)
(declare-fun S (StrSlice) Poly)
(declare-fun %S (Poly) StrSlice)
(declare-fun C (Char) Poly)
(declare-fun %C (Poly) Char)
(declare-sort Type 0)
(declare-const BOOL Type)
(declare-const INT Type)
(declare-const NAT Type)
(declare-const STRSLICE Type)
(declare-const CHAR Type)
(declare-fun UINT (Int) Type)
(declare-fun SINT (Int) Type)
(declare-fun CONST_INT (Int) Type)
(declare-sort Dcr 0)
(declare-const $ Dcr)
(declare-fun REF (Dcr) Dcr)
(declare-fun MUT_REF (Dcr) Dcr)
(declare-fun BOX (Dcr) Dcr)
(declare-fun RC (Dcr) Dcr)
(declare-fun ARC (Dcr) Dcr)
(declare-fun GHOST (Dcr) Dcr)
(declare-fun TRACKED (Dcr) Dcr)
(declare-fun NEVER (Dcr) Dcr)
(declare-fun ARRAY (Dcr Type Dcr Type) Type)
(declare-fun SLICE (Dcr Type) Type)
(declare-fun has_type (Poly Type) Bool)
(declare-fun as_type (Poly Type) Poly)
(declare-fun mk_fun (%%Function%%) %%Function%%)
(declare-fun const_int (Type) Int)
(assert (forall ((i Int)) (! (= i (const_int (CONST_INT i))) :pattern ((CONST_INT i)) :qid prelude_type_id_const_int :skolemid skolem_prelude_type_id_const_int)))
(assert (forall ((b Bool)) (! (has_type (B b) BOOL) :pattern ((has_type (B b) BOOL)) :qid prelude_has_type_bool :skolemid skolem_prelude_has_type_bool)))
(assert (forall ((x Poly) (t Type)) (! (and (has_type (as_type x t) t) (=> (has_type x t) (= x (as_type x t)))) :pattern ((as_type x t)) :qid prelude_as_type :skolemid skolem_prelude_as_type)))
(assert (forall ((x %%Function%%)) (! (= (mk_fun x) x) :pattern ((mk_fun x)) :qid prelude_mk_fun :skolemid skolem_prelude_mk_fun)))
(assert (forall ((x Bool)) (! (= x (%B (B x))) :pattern ((B x)) :qid prelude_unbox_box_bool :skolemid skolem_prelude_unbox_box_bool)))
(assert (forall ((x Int)) (! (= x (%I (I x))) :pattern ((I x)) :qid prelude_unbox_box_int :skolemid skolem_prelude_unbox_box_int)))
(assert (forall ((x Poly)) (! (=> (has_type x BOOL) (= x (B (%B x)))) :pattern ((has_type x BOOL)) :qid prelude_box_unbox_bool :skolemid skolem_prelude_box_unbox_bool)))
(assert (forall ((x Poly)) (! (=> (has_type x INT) (= x (I (%I x)))) :pattern ((has_type x INT)) :qid prelude_box_unbox_int :skolemid skolem_prelude_box_unbox_int)))
(assert (forall ((x Poly)) (! (=> (has_type x NAT) (= x (I (%I x)))) :pattern ((has_type x NAT)) :qid prelude_box_unbox_nat :skolemid skolem_prelude_box_unbox_nat)))
(assert (forall ((bits Int) (x Poly)) (! (=> (has_type x (UINT bits)) (= x (I (%I x)))) :pattern ((has_type x (UINT bits))) :qid prelude_box_unbox_uint :skolemid skolem_prelude_box_unbox_uint)))
(assert (forall ((bits Int) (x Poly)) (! (=> (has_type x (SINT bits)) (= x (I (%I x)))) :pattern ((has_type x (SINT bits))) :qid prelude_box_unbox_sint :skolemid skolem_prelude_box_unbox_sint)))
(assert (forall ((x Int)) (! (= (str%from_strlit (str%new_strlit x)) x) :pattern ((str%new_strlit x)) :qid prelude_strlit_injective :skolemid skolem_prelude_strlit_injective)))
(assert (forall ((x Poly)) (! (=> (has_type x STRSLICE) (= x (S (%S x)))) :pattern ((has_type x STRSLICE)) :qid prelude_box_unbox_strslice :skolemid skolem_prelude_box_unbox_strslice)))
(assert (forall ((x StrSlice)) (! (= x (%S (S x))) :pattern ((S x)) :qid prelude_unbox_box_strslice :skolemid skolem_prelude_unbox_box_strslice)))
(assert (forall ((x StrSlice)) (! (has_type (S x) STRSLICE) :pattern ((has_type (S x) STRSLICE)) :qid prelude_has_type_strslice :skolemid skolem_prelude_has_type_strslice)))
(declare-fun ext_eq (Bool Type Poly Poly) Bool)
(assert (forall ((deep Bool) (t Type) (x Poly) (y Poly)) (! (= (= x y) (ext_eq deep t x y)) :pattern ((ext_eq deep t x y)) :qid prelude_ext_eq :skolemid skolem_prelude_ext_eq)))
(declare-const SZ Int)
(assert (or (= SZ 32) (= SZ 64)))
(declare-fun uHi (Int) Int)
(declare-fun iLo (Int) Int)
(declare-fun iHi (Int) Int)
(assert (= (uHi 8) 256))
(assert (= (uHi 16) 65536))
(assert (= (uHi 32) 4294967296))
(assert (= (uHi 64) 18446744073709551616))
(assert (= (uHi 128) (+ 1 340282366920938463463374607431768211455)))
(assert (= (iLo 8) (- 128)))
(assert (= (iLo 16) (- 32768)))
(assert (= (iLo 32) (- 2147483648)))
(assert (= (iLo 64) (- 9223372036854775808)))
(assert (= (iLo 128) (- 170141183460469231731687303715884105728)))
(assert (= (iHi 8) 128))
(assert (= (iHi 16) 32768))
(assert (= (iHi 32) 2147483648))
(assert (= (iHi 64) 9223372036854775808))
(assert (= (iHi 128) 170141183460469231731687303715884105728))
(declare-fun nClip (Int) Int)
(declare-fun uClip (Int Int) Int)
(declare-fun iClip (Int Int) Int)
(assert (forall ((i Int)) (! (and (<= 0 (nClip i)) (=> (<= 0 i) (= i (nClip i)))) :pattern ((nClip i)) :qid prelude_nat_clip :skolemid skolem_prelude_nat_clip)))
(assert (forall ((bits Int) (i Int)) (! (and (<= 0 (uClip bits i)) (< (uClip bits i) (uHi bits)) (=> (and (<= 0 i) (< i (uHi bits))) (= i (uClip bits i)))) :pattern ((uClip bits i)) :qid prelude_u_clip :skolemid skolem_prelude_u_clip)))
(assert (forall ((bits Int) (i Int)) (! (and (<= (iLo bits) (iClip bits i)) (< (iClip bits i) (iHi bits)) (=> (and (<= (iLo bits) i) (< i (iHi bits))) (= i (iClip bits i)))) :pattern ((iClip bits i)) :qid prelude_i_clip :skolemid skolem_prelude_i_clip)))
(declare-fun uInv (Int Int) Bool)
(declare-fun iInv (Int Int) Bool)
(assert (forall ((bits Int) (i Int)) (! (= (uInv bits i) (and (<= 0 i) (< i (uHi bits)))) :pattern ((uInv bits i)) :qid prelude_u_inv :skolemid skolem_prelude_u_inv)))
(assert (forall ((bits Int) (i Int)) (! (= (iInv bits i) (and (<= (iLo bits) i) (< i (iHi bits)))) :pattern ((iInv bits i)) :qid prelude_i_inv :skolemid skolem_prelude_i_inv)))
(assert (forall ((x Int)) (! (has_type (I x) INT) :pattern ((has_type (I x) INT)) :qid prelude_has_type_int :skolemid skolem_prelude_has_type_int)))
(assert (forall ((x Int)) (! (=> (<= 0 x) (has_type (I x) NAT)) :pattern ((has_type (I x) NAT)) :qid prelude_has_type_nat :skolemid skolem_prelude_has_type_nat)))
(assert (forall ((bits Int) (x Int)) (! (=> (uInv bits x) (has_type (I x) (UINT bits))) :pattern ((has_type (I x) (UINT bits))) :qid prelude_has_type_uint :skolemid skolem_prelude_has_type_uint)))
(assert (forall ((bits Int) (x Int)) (! (=> (iInv bits x) (has_type (I x) (SINT bits))) :pattern ((has_type (I x) (SINT bits))) :qid prelude_has_type_sint :skolemid skolem_prelude_has_type_sint)))
(assert (forall ((x Poly)) (! (=> (has_type x NAT) (<= 0 (%I x))) :pattern ((has_type x NAT)) :qid prelude_unbox_int :skolemid skolem_prelude_unbox_int)))
(assert (forall ((bits Int) (x Poly)) (! (=> (has_type x (UINT bits)) (uInv bits (%I x))) :pattern ((has_type x (UINT bits))) :qid prelude_unbox_uint :skolemid skolem_prelude_unbox_uint)))
(assert (forall ((bits Int) (x Poly)) (! (=> (has_type x (SINT bits)) (iInv bits (%I x))) :pattern ((has_type x (SINT bits))) :qid prelude_unbox_sint :skolemid skolem_prelude_unbox_sint)))
(declare-fun Add (Int Int) Int)
(declare-fun Sub (Int Int) Int)
(declare-fun Mul (Int Int) Int)
(declare-fun EucDiv (Int Int) Int)
(declare-fun EucMod (Int Int) Int)
(assert (forall ((x Int) (y Int)) (! (= (Add x y) (+ x y)) :pattern ((Add x y)) :qid prelude_add :skolemid skolem_prelude_add)))
(assert (forall ((x Int) (y Int)) (! (= (Sub x y) (- x y)) :pattern ((Sub x y)) :qid prelude_sub :skolemid skolem_prelude_sub)))
(assert (forall ((x Int) (y Int)) (! (= (Mul x y) (* x y)) :pattern ((Mul x y)) :qid prelude_mul :skolemid skolem_prelude_mul)))
(assert (forall ((x Int) (y Int)) (! (= (EucDiv x y) (div x y)) :pattern ((EucDiv x y)) :qid prelude_eucdiv :skolemid skolem_prelude_eucdiv)))
(assert (forall ((x Int) (y Int)) (! (= (EucMod x y) (mod x y)) :pattern ((EucMod x y)) :qid prelude_eucmod :skolemid skolem_prelude_eucmod)))
(assert (forall ((x Int) (y Int)) (! (=> (and (<= 0 x) (<= 0 y)) (<= 0 (Mul x y))) :pattern ((Mul x y)) :qid prelude_mul_nats :skolemid skolem_prelude_mul_nats)))
(assert (forall ((x Int) (y Int)) (! (=> (and (<= 0 x) (< 0 y)) (and (<= 0 (EucDiv x y)) (<= (EucDiv x y) x))) :pattern ((EucDiv x y)) :qid prelude_div_unsigned_in_bounds :skolemid skolem_prelude_div_unsigned_in_bounds)))
(assert (forall ((x Int) (y Int)) (! (=> (and (<= 0 x) (< 0 y)) (and (<= 0 (EucMod x y)) (< (EucMod x y) y))) :pattern ((EucMod x y)) :qid prelude_mod_unsigned_in_bounds :skolemid skolem_prelude_mod_unsigned_in_bounds)))
(assert (forall ((x Poly)) (! (=> (has_type x CHAR) (= x (C (%C x)))) :pattern ((has_type x CHAR)) :qid prelude_box_unbox_char :skolemid skolem_prelude_box_unbox_char)))
(assert (forall ((x Char)) (! (= x (%C (C x))) :pattern ((C x)) :qid prelude_unbox_box_char :skolemid skolem_prelude_unbox_box_char)))
(assert (forall ((x Char)) (! (has_type (C x) CHAR) :pattern ((has_type (C x) CHAR)) :qid prelude_has_type_char :skolemid skolem_prelude_has_type_char)))
(assert (forall ((x Int)) (! (=> (and (<= 0 x) (< x (uHi 32))) (= x (char%to_unicode (char%from_unicode x)))) :pattern ((char%from_unicode x)) :qid prelude_char_injective :skolemid skolem_prelude_char_injective)))
(assert (forall ((c Char)) (! (and (<= 0 (char%to_unicode c)) (< (char%to_unicode c) (uHi 32))) :pattern ((char%to_unicode c)) :qid prelude_to_unicode_bounds :skolemid skolem_prelude_to_unicode_bounds)))
(declare-fun height (Poly) Height)
(declare-fun height_lt (Height Height) Bool)
(assert (forall ((x Height) (y Height)) (! (= (height_lt x y) (and ((_ partial-order 0) x y) (not (= x y)))) :pattern ((height_lt x y)) :qid prelude_height_lt :skolemid skolem_prelude_height_lt)))
(declare-fun fun_from_recursive_field (Poly) Poly)
(declare-fun check_decrease_int (Int Int Bool) Bool)
(assert (forall ((cur Int) (prev Int) (otherwise Bool)) (! (= (check_decrease_int cur prev otherwise) (or (and (<= 0 cur) (< cur prev)) (and (= cur prev) otherwise))) :pattern ((check_decrease_int cur prev otherwise)) :qid prelude_check_decrease_int :skolemid skolem_prelude_check_decrease_int)))
(declare-fun check_decrease_height (Poly Poly Bool) Bool)
(assert (forall ((cur Poly) (prev Poly) (otherwise Bool)) (! (= (check_decrease_height cur prev otherwise) (or (height_lt (height cur) (height prev)) (and (= (height cur) (height prev)) otherwise))) :pattern ((check_decrease_height cur prev otherwise)) :qid prelude_check_decrease_height :skolemid skolem_prelude_check_decrease_height)))
(declare-fun uintxor (Int Poly Poly) Int)
(declare-fun uintand (Int Poly Poly) Int)
(declare-fun uintor (Int Poly Poly) Int)
(declare-fun uintshr (Int Poly Poly) Int)
(declare-fun uintshl (Int Poly Poly) Int)
(declare-fun uintnot (Int Poly) Int)
(declare-fun singular_mod (Int Int) Int)
(assert (forall ((x Int) (y Int)) (! (=> (not (= y 0)) (= (EucMod x y) (singular_mod x y))) :pattern ((singular_mod x y)) :qid prelude_singularmod :skolemid skolem_prelude_singularmod)))
(declare-fun closure_req (Type Dcr Type Poly Poly) Bool)
(declare-fun closure_ens (Type Dcr Type Poly Poly Poly) Bool)
(set-info :comment ";; MODULE 'root module'")
(set-info :comment ";; Fuel")
(assert true)
(set-info :comment ";; Datatypes")
(declare-datatypes ((tuple%0. 0)) (((tuple%0./tuple%0 ))))
(declare-const TYPE%tuple%0. Type)
(declare-fun Poly%tuple%0. (tuple%0.) Poly)
(declare-fun %Poly%tuple%0. (Poly) tuple%0.)
(assert (forall ((x@ tuple%0.)) (! (= x@ (%Poly%tuple%0. (Poly%tuple%0. x@))) :pattern ((Poly%tuple%0. x@)) :qid internal_crate__tuple__0_box_axiom_definition :skolemid skolem_internal_crate__tuple__0_box_axiom_definition)))
(assert (forall ((x@ Poly)) (! (=> (has_type x@ TYPE%tuple%0.) (= x@ (Poly%tuple%0. (%Poly%tuple%0. x@)))) :pattern ((has_type x@ TYPE%tuple%0.)) :qid internal_crate__tuple__0_unbox_axiom_definition :skolemid skolem_internal_crate__tuple__0_unbox_axiom_definition)))
(assert (forall ((x@ tuple%0.)) (! (has_type (Poly%tuple%0. x@) TYPE%tuple%0.) :pattern ((has_type (Poly%tuple%0. x@) TYPE%tuple%0.)) :qid internal_crate__tuple__0_has_type_always_definition :skolemid skolem_internal_crate__tuple__0_has_type_always_definition)))
(set-info :comment ";; Function-Specs main::nl_basics::lemma_mul_properties_auto_1")
(declare-fun ens%main!nl_basics.lemma_mul_properties_auto_1. (Int) Bool)
(assert (forall ((no%param@ Int)) (! (= (ens%main!nl_basics.lemma_mul_properties_auto_1. no%param@) (and (forall ((x~14$ Int) (y~16$ Int)) (! (= (Mul x~14$ y~16$) (Mul y~16$ x~14$)) :pattern ((Mul x~14$ y~16$)) :qid user_main__nl_basics__lemma_mul_properties_auto_1_0 :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_0)) (forall ((x~45$ Int) (y~47$ Int) (z~49$ Int)) (! (= (Mul x~45$ (Mul y~47$ z~49$)) (Mul (Mul x~45$ y~47$) z~49$)) :pattern ((Mul x~45$ (Mul y~47$ z~49$))) :qid user_main__nl_basics__lemma_mul_properties_auto_1_1 :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_1)) (forall ((x~88$ Int) (y~90$ Int) (z~92$ Int)) (! (= (Mul x~88$ (Mul y~90$ z~92$)) (Mul (Mul x~88$ y~90$) z~92$)) :pattern ((Mul (Mul x~88$ y~90$) z~92$)) :qid user_main__nl_basics__lemma_mul_properties_auto_1_2 :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_2)) (forall ((x~131$ Int) (y~133$ Int) (z~135$ Int)) (! (= (Mul x~131$ (Add y~133$ z~135$)) (Add (Mul x~131$ y~133$) (Mul x~131$ z~135$))) :pattern ((Mul x~131$ (Add y~133$ z~135$))) :qid user_main__nl_basics__lemma_mul_properties_auto_1_3 :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_3)) (forall ((x~178$ Int) (y~180$ Int) (z~182$ Int)) (! (= (Mul (Add x~178$ y~180$) z~182$) (Add (Mul x~178$ z~182$) (Mul y~180$ z~182$))) :pattern ((Mul (Add x~178$ y~180$) z~182$)) :qid user_main__nl_basics__lemma_mul_properties_auto_1_4 :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_4)) (forall ((x~225$ Int) (y~227$ Int) (z~229$ Int)) (! (= (Mul x~225$ (Sub y~227$ z~229$)) (Sub (Mul x~225$ y~227$) (Mul x~225$ z~229$))) :pattern ((Mul x~225$ (Sub y~227$ z~229$))) :qid user_main__nl_basics__lemma_mul_properties_auto_1_5 :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_5)) (forall ((x~272$ Int) (y~274$ Int) (z~276$ Int)) (! (= (Mul (Sub x~272$ y~274$) z~276$) (Sub (Mul x~272$ z~276$) (Mul y~274$ z~276$))) :pattern ((Mul (Sub x~272$ y~274$) z~276$)) :qid user_main__nl_basics__lemma_mul_properties_auto_1_6 :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_6)) (forall ((x~319$ Int) (y~321$ Int) (z~323$ Int)) (! (= (Mul x~319$ (Add y~321$ z~323$)) (Add (Mul x~319$ y~321$) (Mul x~319$ z~323$))) :pattern ((Add (Mul x~319$ y~321$) (Mul x~319$ z~323$))) :qid user_main__nl_basics__lemma_mul_properties_auto_1_7 :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_7)) (forall ((x~366$ Int) (y~368$ Int) (z~370$ Int)) (! (= (Mul (Add x~366$ y~368$) z~370$) (Add (Mul x~366$ z~370$) (Mul y~368$ z~370$))) :pattern ((Add (Mul x~366$ z~370$) (Mul y~368$ z~370$))) :qid user_main__nl_basics__lemma_mul_properties_auto_1_8 :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_8)) (forall ((x~413$ Int) (y~415$ Int) (z~417$ Int)) (! (= (Mul x~413$ (Sub y~415$ z~417$)) (Sub (Mul x~413$ y~415$) (Mul x~413$ z~417$))) :pattern ((Sub (Mul x~413$ y~415$) (Mul x~413$ z~417$))) :qid user_main__nl_basics__lemma_mul_properties_auto_1_9 :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_9)) (forall ((x~460$ Int) (y~462$ Int) (z~464$ Int)) (! (= (Mul (Sub x~460$ y~462$) z~464$) (Sub (Mul x~460$ z~464$) (Mul y~462$ z~464$))) :pattern ((Sub (Mul x~460$ z~464$) (Mul y~462$ z~464$))) :qid user_main__nl_basics__lemma_mul_properties_auto_1_10 :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_10)))) :pattern ((ens%main!nl_basics.lemma_mul_properties_auto_1. no%param@)) :qid internal_ens__main!nl_basics.lemma_mul_properties_auto_1._definition :skolemid skolem_internal_ens__main!nl_basics.lemma_mul_properties_auto_1._definition)))
(set-info :comment ";; Function-Def main::auto_0")
(set-info :comment ";; mariposa_data/v_nl//12091294745012006478/nlqi_verus/src/main.rs:7:1: 36:40 (#0)")
(push 1)
(declare-const a0~2@ Int)
(declare-const b0~4@ Int)
(declare-const c0~6@ Int)
(declare-const d0~8@ Int)
(declare-const a1~10@ Int)
(declare-const b1~12@ Int)
(declare-const c1~14@ Int)
(declare-const d1~16@ Int)
(declare-const a2~18@ Int)
(declare-const b2~20@ Int)
(declare-const c2~22@ Int)
(declare-const d2~24@ Int)
(declare-const a3~26@ Int)
(declare-const b3~28@ Int)
(declare-const c3~30@ Int)
(declare-const d3~32@ Int)
(declare-const a4~34@ Int)
(declare-const b4~36@ Int)
(declare-const c4~38@ Int)
(declare-const d4~40@ Int)
(declare-const a5~42@ Int)
(declare-const b5~44@ Int)
(declare-const c5~46@ Int)
(declare-const d5~48@ Int)
(declare-const a6~50@ Int)
(declare-const b6~52@ Int)
(declare-const c6~54@ Int)
(declare-const d6~56@ Int)
(declare-const a7~58@ Int)
(declare-const b7~60@ Int)
(declare-const c7~62@ Int)
(declare-const d7~64@ Int)
(declare-const a8~66@ Int)
(declare-const b8~68@ Int)
(declare-const c8~70@ Int)
(declare-const d8~72@ Int)
(declare-const a9~74@ Int)
(declare-const b9~76@ Int)
(declare-const c9~78@ Int)
(declare-const d9~80@ Int)
(declare-const a10~82@ Int)
(declare-const b10~84@ Int)
(declare-const c10~86@ Int)
(declare-const d10~88@ Int)
(declare-const a11~90@ Int)
(declare-const b11~92@ Int)
(declare-const c11~94@ Int)
(declare-const d11~96@ Int)
(declare-const a12~98@ Int)
(declare-const b12~100@ Int)
(declare-const c12~102@ Int)
(declare-const d12~104@ Int)
(declare-const a13~106@ Int)
(declare-const b13~108@ Int)
(declare-const c13~110@ Int)
(declare-const d13~112@ Int)
(declare-const a14~114@ Int)
(declare-const b14~116@ Int)
(declare-const c14~118@ Int)
(declare-const d14~120@ Int)
(declare-const a15~122@ Int)
(declare-const b15~124@ Int)
(declare-const c15~126@ Int)
(declare-const d15~128@ Int)
(declare-const a16~130@ Int)
(declare-const b16~132@ Int)
(declare-const c16~134@ Int)
(declare-const d16~136@ Int)
(declare-const a17~138@ Int)
(declare-const b17~140@ Int)
(declare-const c17~142@ Int)
(declare-const d17~144@ Int)
(declare-const a18~146@ Int)
(declare-const b18~148@ Int)
(declare-const c18~150@ Int)
(declare-const d18~152@ Int)
(declare-const a19~154@ Int)
(declare-const b19~156@ Int)
(declare-const c19~158@ Int)
(declare-const d19~160@ Int)
(declare-const a20~162@ Int)
(declare-const b20~164@ Int)
(declare-const c20~166@ Int)
(declare-const d20~168@ Int)
(declare-const a21~170@ Int)
(declare-const b21~172@ Int)
(declare-const c21~174@ Int)
(declare-const d21~176@ Int)
(declare-const a22~178@ Int)
(declare-const b22~180@ Int)
(declare-const c22~182@ Int)
(declare-const d22~184@ Int)
(declare-const a23~186@ Int)
(declare-const b23~188@ Int)
(declare-const c23~190@ Int)
(declare-const d23~192@ Int)
(declare-const a24~194@ Int)
(declare-const b24~196@ Int)
(declare-const c24~198@ Int)
(declare-const d24~200@ Int)
(declare-const a25~202@ Int)
(declare-const b25~204@ Int)
(declare-const c25~206@ Int)
(declare-const d25~208@ Int)
(declare-const a26~210@ Int)
(declare-const b26~212@ Int)
(declare-const c26~214@ Int)
(declare-const d26~216@ Int)
(declare-const a27~218@ Int)
(declare-const b27~220@ Int)
(declare-const c27~222@ Int)
(declare-const d27~224@ Int)
(declare-const a28~226@ Int)
(declare-const b28~228@ Int)
(declare-const c28~230@ Int)
(declare-const d28~232@ Int)
(declare-const a29~234@ Int)
(declare-const b29~236@ Int)
(declare-const c29~238@ Int)
(declare-const d29~240@ Int)
(declare-const temp_0_0~305@ Int)
(declare-const temp_0_1~370@ Int)
(declare-const temp_1_0~455@ Int)
(declare-const temp_1_1~528@ Int)
(declare-const temp_2_0~617@ Int)
(declare-const temp_2_1~682@ Int)
(declare-const temp_3_0~759@ Int)
(declare-const temp_3_1~812@ Int)
(declare-const temp_4_0~901@ Int)
(declare-const temp_4_1~966@ Int)
(declare-const temp_5_0~1039@ Int)
(declare-const temp_5_1~1088@ Int)
(declare-const temp_6_0~1177@ Int)
(declare-const temp_6_1~1242@ Int)
(declare-const temp_7_0~1331@ Int)
(declare-const temp_7_1~1396@ Int)
(declare-const temp_8_0~1493@ Int)
(declare-const temp_8_1~1594@ Int)
(declare-const temp_9_0~1683@ Int)
(declare-const temp_9_1~1748@ Int)
(declare-const temp_10_0~1841@ Int)
(declare-const temp_10_1~1910@ Int)
(declare-const temp_11_0~1991@ Int)
(declare-const temp_11_1~2048@ Int)
(declare-const temp_12_0~2133@ Int)
(declare-const temp_12_1~2194@ Int)
(declare-const temp_13_0~2279@ Int)
(declare-const temp_13_1~2340@ Int)
(declare-const temp_14_0~2429@ Int)
(declare-const temp_14_1~2494@ Int)
(declare-const temp_15_0~2579@ Int)
(declare-const temp_15_1~2640@ Int)
(declare-const temp_16_0~2753@ Int)
(declare-const temp_16_1~2842@ Int)
(declare-const temp_17_0~2923@ Int)
(declare-const temp_17_1~2980@ Int)
(declare-const temp_18_0~3069@ Int)
(declare-const temp_18_1~3134@ Int)
(declare-const temp_19_0~3219@ Int)
(declare-const temp_19_1~3280@ Int)
(declare-const temp_20_0~3377@ Int)
(declare-const temp_20_1~3450@ Int)
(declare-const temp_21_0~3551@ Int)
(declare-const temp_21_1~3656@ Int)
(declare-const temp_22_0~3745@ Int)
(declare-const temp_22_1~3810@ Int)
(declare-const temp_23_0~3895@ Int)
(declare-const temp_23_1~3956@ Int)
(assert fuel_defaults)
(set-info :comment ";; assertion failed")
(declare-const %%location_label%%0 Bool)
(set-info :comment ";; assertion failed")
(declare-const %%location_label%%1 Bool)
(set-info :comment ";; assertion failed")
(declare-const %%location_label%%2 Bool)
(set-info :comment ";; assertion failed")
(declare-const %%location_label%%3 Bool)
(set-info :comment ";; assertion failed")
(declare-const %%location_label%%4 Bool)
(set-info :comment ";; assertion failed")
(declare-const %%location_label%%5 Bool)
(set-info :comment ";; assertion failed")
(declare-const %%location_label%%6 Bool)
(set-info :comment ";; assertion failed")
(declare-const %%location_label%%7 Bool)
(set-info :comment ";; assertion failed")
(declare-const %%location_label%%8 Bool)
(set-info :comment ";; assertion failed")
(declare-const %%location_label%%9 Bool)
(set-info :comment ";; assertion failed")
(declare-const %%location_label%%10 Bool)
(set-info :comment ";; assertion failed")
(declare-const %%location_label%%11 Bool)
(set-info :comment ";; assertion failed")
(declare-const %%location_label%%12 Bool)
(set-info :comment ";; assertion failed")
(declare-const %%location_label%%13 Bool)
(set-info :comment ";; assertion failed")
(declare-const %%location_label%%14 Bool)
(set-info :comment ";; assertion failed")
(declare-const %%location_label%%15 Bool)
(set-info :comment ";; assertion failed")
(declare-const %%location_label%%16 Bool)
(set-info :comment ";; assertion failed")
(declare-const %%location_label%%17 Bool)
(set-info :comment ";; assertion failed")
(declare-const %%location_label%%18 Bool)
(set-info :comment ";; assertion failed")
(declare-const %%location_label%%19 Bool)
(set-info :comment ";; assertion failed")
(declare-const %%location_label%%20 Bool)
(set-info :comment ";; assertion failed")
(declare-const %%location_label%%21 Bool)
(set-info :comment ";; assertion failed")
(declare-const %%location_label%%22 Bool)
(set-info :comment ";; assertion failed")
(declare-const %%location_label%%23 Bool)
(declare-const %%query%% Bool)
(assert (=> %%query%% (not (=> (= temp_0_0~305@ (Sub (Sub (Mul (Mul c0~6@ c0~6@) (Mul c0~6@ b0~4@)) (Mul (Mul a0~2@ d0~8@) (Mul b0~4@ b0~4@))) (Mul (Mul (Mul b0~4@ a0~2@) (Sub d0~8@ d0~8@)) (Mul (Mul d0~8@ a0~2@) (Mul b0~4@ b0~4@))))) (=> (= temp_0_1~370@ (Sub (Sub (Mul (Mul c0~6@ c0~6@) (Mul c0~6@ b0~4@)) (Mul (Mul a0~2@ d0~8@) (Mul b0~4@ b0~4@))) (Mul (Mul (Mul a0~2@ b0~4@) (Sub d0~8@ d0~8@)) (Mul (Mul d0~8@ a0~2@) (Mul b0~4@ b0~4@))))) (and (=> (ens%main!nl_basics.lemma_mul_properties_auto_1. 0) (=> %%location_label%%0 (= temp_0_0~305@ temp_0_1~370@))) (=> (= temp_0_0~305@ temp_0_1~370@) (=> (= temp_1_0~455@ (Sub (Mul (Mul (Add b1~12@ b1~12@) (Add c1~14@ c1~14@)) (Sub (Mul a1~10@ b1~12@) (Mul d1~16@ d1~16@))) (Mul (Sub (Mul b1~12@ c1~14@) (Mul c1~14@ b1~12@)) (Mul d1~16@ (Mul a1~10@ a1~10@))))) (=> (= temp_1_1~528@ (Sub (Mul (Mul (Add b1~12@ b1~12@) (Add c1~14@ c1~14@)) (Sub (Mul a1~10@ b1~12@) (Mul d1~16@ d1~16@))) (Sub (Mul (Mul b1~12@ c1~14@) (Mul d1~16@ (Mul a1~10@ a1~10@))) (Mul (Mul c1~14@ b1~12@) (Mul d1~16@ (Mul a1~10@ a1~10@)))))) (and (=> (ens%main!nl_basics.lemma_mul_properties_auto_1. 0) (=> %%location_label%%1 (= temp_1_0~455@ temp_1_1~528@))) (=> (= temp_1_0~455@ temp_1_1~528@) (=> (= temp_2_0~617@ (Mul (Add (Mul (Mul b2~20@ d2~24@) (Mul c2~22@ a2~18@)) (Mul (Mul b2~20@ a2~18@) (Mul b2~20@ d2~24@))) (Mul (Mul (Mul b2~20@ d2~24@) (Sub a2~18@ b2~20@)) (Mul (Add a2~18@ c2~22@) (Mul c2~22@ d2~24@))))) (=> (= temp_2_1~682@ (Mul (Add (Mul (Mul b2~20@ d2~24@) (Mul c2~22@ a2~18@)) (Mul (Mul b2~20@ a2~18@) (Mul b2~20@ d2~24@))) (Mul (Mul (Mul b2~20@ d2~24@) (Sub a2~18@ b2~20@)) (Mul (Mul (Add a2~18@ c2~22@) c2~22@) d2~24@)))) (and (=> (ens%main!nl_basics.lemma_mul_properties_auto_1. 0) (=> %%location_label%%2 (= temp_2_0~617@ temp_2_1~682@))) (=> (= temp_2_0~617@ temp_2_1~682@) (=> (= temp_3_0~759@ (Mul (Mul (Mul (Add c3~30@ d3~32@) (Mul d3~32@ d3~32@)) b3~28@) (Mul (Mul (Add b3~28@ d3~32@) (Mul b3~28@ c3~30@)) (Mul (Mul d3~32@ d3~32@) (Mul b3~28@ b3~28@))))) (=> (= temp_3_1~812@ (Mul (Mul (Mul (Add c3~30@ d3~32@) (Mul d3~32@ d3~32@)) b3~28@) (Mul (Mul (Add b3~28@ d3~32@) (Mul b3~28@ c3~30@)) (Mul d3~32@ (Mul d3~32@ (Mul b3~28@ b3~28@)))))) (and (=> (ens%main!nl_basics.lemma_mul_properties_auto_1. 0) (=> %%location_label%%3 (= temp_3_0~759@ temp_3_1~812@))) (=> (= temp_3_0~759@ temp_3_1~812@) (=> (= temp_4_0~901@ (Add (Mul (Mul (Mul d4~40@ d4~40@) (Mul c4~38@ b4~36@)) (Mul (Mul b4~36@ a4~34@) (Add d4~40@ a4~34@))) (Add (Mul (Mul b4~36@ d4~40@) (Mul c4~38@ c4~38@)) (Mul (Mul b4~36@ c4~38@) (Mul b4~36@ d4~40@))))) (=> (= temp_4_1~966@ (Add (Mul (Mul (Mul d4~40@ d4~40@) (Mul c4~38@ b4~36@)) (Mul (Mul b4~36@ a4~34@) (Add d4~40@ a4~34@))) (Add (Mul (Mul b4~36@ d4~40@) (Mul c4~38@ c4~38@)) (Mul b4~36@ (Mul c4~38@ (Mul b4~36@ d4~40@)))))) (and (=> (ens%main!nl_basics.lemma_mul_properties_auto_1. 0) (=> %%location_label%%4 (= temp_4_0~901@ temp_4_1~966@))) (=> (= temp_4_0~901@ temp_4_1~966@) (=> (= temp_5_0~1039@ (Mul (Mul (Mul (Mul b5~44@ b5~44@) (Sub c5~46@ d5~48@)) c5~46@) (Mul (Sub a5~42@ (Mul b5~44@ a5~42@)) (Sub (Mul b5~44@ d5~48@) (Mul a5~42@ c5~46@))))) (=> (= temp_5_1~1088@ (Mul (Mul (Sub a5~42@ (Mul b5~44@ a5~42@)) (Sub (Mul b5~44@ d5~48@) (Mul a5~42@ c5~46@))) (Mul (Mul (Mul b5~44@ b5~44@) (Sub c5~46@ d5~48@)) c5~46@))) (and (=> (ens%main!nl_basics.lemma_mul_properties_auto_1. 0) (=> %%location_label%%5 (= temp_5_0~1039@ temp_5_1~1088@))) (=> (= temp_5_0~1039@ temp_5_1~1088@) (=> (= temp_6_0~1177@ (Mul (Add (Mul (Sub d6~56@ a6~50@) (Mul d6~56@ d6~56@)) (Mul (Mul a6~50@ a6~50@) (Mul b6~52@ d6~56@))) (Mul (Add (Add a6~50@ b6~52@) (Mul a6~50@ b6~52@)) (Mul (Mul b6~52@ a6~50@) (Sub a6~50@ d6~56@))))) (=> (= temp_6_1~1242@ (Mul (Add (Mul (Sub d6~56@ a6~50@) (Mul d6~56@ d6~56@)) (Mul (Mul a6~50@ a6~50@) (Mul b6~52@ d6~56@))) (Mul (Add (Add a6~50@ b6~52@) (Mul a6~50@ b6~52@)) (Mul (Mul b6~52@ a6~50@) (Sub a6~50@ d6~56@))))) (and (=> (ens%main!nl_basics.lemma_mul_properties_auto_1. 0) (=> %%location_label%%6 (= temp_6_0~1177@ temp_6_1~1242@))) (=> (= temp_6_0~1177@ temp_6_1~1242@) (=> (= temp_7_0~1331@ (Mul (Mul (Mul (Mul b7~60@ c7~62@) (Mul c7~62@ d7~64@)) (Mul (Sub c7~62@ d7~64@) (Mul a7~58@ b7~60@))) (Mul (Mul (Mul a7~58@ d7~64@) (Mul c7~62@ b7~60@)) (Mul (Mul c7~62@ b7~60@) (Mul d7~64@ b7~60@))))) (=> (= temp_7_1~1396@ (Mul (Mul (Mul (Mul (Mul b7~60@ c7~62@) (Mul c7~62@ d7~64@)) (Sub c7~62@ d7~64@)) (Mul a7~58@ b7~60@)) (Mul (Mul (Mul a7~58@ d7~64@) (Mul c7~62@ b7~60@)) (Mul (Mul c7~62@ b7~60@) (Mul d7~64@ b7~60@))))) (and (=> (ens%main!nl_basics.lemma_mul_properties_auto_1. 0) (=> %%location_label%%7 (= temp_7_0~1331@ temp_7_1~1396@))) (=> (= temp_7_0~1331@ temp_7_1~1396@) (=> (= temp_8_0~1493@ (Mul (Sub (Add (Mul d8~72@ d8~72@) (Mul d8~72@ a8~66@)) (Mul (Mul 82 c8~70@) (Add c8~70@ b8~68@))) (Mul (Mul d8~72@ (Mul b8~68@ b8~68@)) (Mul (Mul d8~72@ c8~70@) (Mul a8~66@ a8~66@))))) (=> (= temp_8_1~1594@ (Sub (Mul (Add (Mul d8~72@ d8~72@) (Mul d8~72@ a8~66@)) (Mul (Mul d8~72@ (Mul b8~68@ b8~68@)) (Mul (Mul d8~72@ c8~70@) (Mul a8~66@ a8~66@)))) (Mul (Mul (Mul 82 c8~70@) (Add c8~70@ b8~68@)) (Mul (Mul d8~72@ (Mul b8~68@ b8~68@)) (Mul (Mul d8~72@ c8~70@) (Mul a8~66@ a8~66@)))))) (and (=> (ens%main!nl_basics.lemma_mul_properties_auto_1. 0) (=> %%location_label%%8 (= temp_8_0~1493@ temp_8_1~1594@))) (=> (= temp_8_0~1493@ temp_8_1~1594@) (=> (= temp_9_0~1683@ (Mul (Add (Sub (Mul d9~80@ c9~78@) (Sub a9~74@ a9~74@)) (Mul (Mul d9~80@ d9~80@) (Mul b9~76@ a9~74@))) (Mul (Mul (Add a9~74@ c9~78@) (Mul b9~76@ b9~76@)) (Mul (Mul d9~80@ d9~80@) (Mul a9~74@ b9~76@))))) (=> (= temp_9_1~1748@ (Mul (Add (Sub (Mul d9~80@ c9~78@) (Sub a9~74@ a9~74@)) (Mul (Mul d9~80@ d9~80@) (Mul a9~74@ b9~76@))) (Mul (Mul (Add a9~74@ c9~78@) (Mul b9~76@ b9~76@)) (Mul (Mul d9~80@ d9~80@) (Mul a9~74@ b9~76@))))) (and (=> (ens%main!nl_basics.lemma_mul_properties_auto_1. 0) (=> %%location_label%%9 (= temp_9_0~1683@ temp_9_1~1748@))) (=> (= temp_9_0~1683@ temp_9_1~1748@) (=> (= temp_10_0~1841@ (Mul (Mul (Mul (Mul a10~82@ 98) (Mul b10~84@ b10~84@)) (Mul b10~84@ (Mul b10~84@ c10~86@))) (Mul (Add (Mul a10~82@ d10~88@) (Mul a10~82@ d10~88@)) (Sub (Mul a10~82@ d10~88@) d10~88@)))) (=> (= temp_10_1~1910@ (Mul (Mul (Mul (Mul a10~82@ 98) (Mul b10~84@ b10~84@)) (Mul (Mul b10~84@ b10~84@) c10~86@)) (Mul (Add (Mul a10~82@ d10~88@) (Mul a10~82@ d10~88@)) (Sub (Mul a10~82@ d10~88@) d10~88@)))) (and (=> (ens%main!nl_basics.lemma_mul_properties_auto_1. 0) (=> %%location_label%%10 (= temp_10_0~1841@ temp_10_1~1910@))) (=> (= temp_10_0~1841@ temp_10_1~1910@) (=> (= temp_11_0~1991@ (Mul (Mul (Mul c11~94@ (Mul a11~90@ a11~90@)) (Mul (Mul b11~92@ b11~92@) (Mul a11~90@ b11~92@))) (Mul (Mul (Mul d11~96@ b11~92@) (Sub d11~96@ d11~96@)) (Mul c11~94@ (Mul d11~96@ c11~94@))))) (=> (= temp_11_1~2048@ (Mul (Mul (Mul c11~94@ (Mul a11~90@ a11~90@)) (Mul (Mul b11~92@ b11~92@) (Mul a11~90@ b11~92@))) (Mul (Mul (Mul d11~96@ b11~92@) (Sub d11~96@ d11~96@)) (Mul c11~94@ (Mul d11~96@ c11~94@))))) (and (=> (ens%main!nl_basics.lemma_mul_properties_auto_1. 0) (=> %%location_label%%11 (= temp_11_0~1991@ temp_11_1~2048@))) (=> (= temp_11_0~1991@ temp_11_1~2048@) (=> (= temp_12_0~2133@ (Mul (Mul (Add (Sub b12~100@ a12~98@) (Mul c12~102@ c12~102@)) (Mul (Mul a12~98@ d12~104@) (Mul a12~98@ a12~98@))) (Mul (Add (Mul c12~102@ d12~104@) (Mul d12~104@ b12~100@)) (Mul (Mul c12~102@ d12~104@) c12~102@)))) (=> (= temp_12_1~2194@ (Mul (Mul (Mul (Add (Sub b12~100@ a12~98@) (Mul c12~102@ c12~102@)) (Mul (Mul a12~98@ d12~104@) (Mul a12~98@ a12~98@))) (Add (Mul c12~102@ d12~104@) (Mul d12~104@ b12~100@))) (Mul (Mul c12~102@ d12~104@) c12~102@))) (and (=> (ens%main!nl_basics.lemma_mul_properties_auto_1. 0) (=> %%location_label%%12 (= temp_12_0~2133@ temp_12_1~2194@))) (=> (= temp_12_0~2133@ temp_12_1~2194@) (=> (= temp_13_0~2279@ (Mul (Mul (Mul (Mul a13~106@ c13~110@) (Mul c13~110@ c13~110@)) (Add (Mul b13~108@ c13~110@) (Add c13~110@ c13~110@))) (Mul (Mul (Mul a13~106@ c13~110@) c13~110@) (Mul (Mul d13~112@ b13~108@) (Add a13~106@ b13~108@))))) (=> (= temp_13_1~2340@ (Mul (Mul (Mul (Mul a13~106@ c13~110@) (Mul c13~110@ c13~110@)) (Add (Mul b13~108@ c13~110@) (Add c13~110@ c13~110@))) (Mul (Mul (Mul c13~110@ a13~106@) c13~110@) (Mul (Mul d13~112@ b13~108@) (Add a13~106@ b13~108@))))) (and (=> (ens%main!nl_basics.lemma_mul_properties_auto_1. 0) (=> %%location_label%%13 (= temp_13_0~2279@ temp_13_1~2340@))) (=> (= temp_13_0~2279@ temp_13_1~2340@) (=> (= temp_14_0~2429@ (Sub (Mul (Mul (Sub c14~118@ c14~118@) (Mul d14~120@ d14~120@)) (Mul (Sub d14~120@ b14~116@) (Mul b14~116@ c14~118@))) (Mul (Mul (Mul c14~118@ c14~118@) (Mul d14~120@ d14~120@)) (Mul (Mul d14~120@ b14~116@) (Mul c14~118@ d14~120@))))) (=> (= temp_14_1~2494@ (Sub (Mul (Mul (Sub c14~118@ c14~118@) (Mul d14~120@ d14~120@)) (Mul (Mul (Sub d14~120@ b14~116@) b14~116@) c14~118@)) (Mul (Mul (Mul c14~118@ c14~118@) (Mul d14~120@ d14~120@)) (Mul (Mul d14~120@ b14~116@) (Mul c14~118@ d14~120@))))) (and (=> (ens%main!nl_basics.lemma_mul_properties_auto_1. 0) (=> %%location_label%%14 (= temp_14_0~2429@ temp_14_1~2494@))) (=> (= temp_14_0~2429@ temp_14_1~2494@) (=> (= temp_15_0~2579@ (Add (Mul (Sub (Mul a15~122@ a15~122@) (Mul a15~122@ d15~128@)) (Mul (Mul c15~126@ d15~128@) b15~124@)) (Mul (Mul (Mul d15~128@ d15~128@) (Add d15~128@ a15~122@)) (Mul (Mul d15~128@ c15~126@) (Mul c15~126@ b15~124@))))) (=> (= temp_15_1~2640@ (Add (Mul (Sub (Mul a15~122@ a15~122@) (Mul a15~122@ d15~128@)) (Mul (Mul c15~126@ d15~128@) b15~124@)) (Mul (Mul (Mul d15~128@ d15~128@) (Add d15~128@ a15~122@)) (Mul (Mul c15~126@ d15~128@) (Mul c15~126@ b15~124@))))) (and (=> (ens%main!nl_basics.lemma_mul_properties_auto_1. 0) (=> %%location_label%%15 (= temp_15_0~2579@ temp_15_1~2640@))) (=> (= temp_15_0~2579@ temp_15_1~2640@) (=> (= temp_16_0~2753@ (Add (Mul (Add (Mul c16~134@ d16~136@) (Mul c16~134@ c16~134@)) (Add (Mul b16~132@ 79) (Mul c16~134@ a16~130@))) (Mul (Sub (Mul a16~130@ b16~132@) (Sub 18 b16~132@)) (Mul (Mul a16~130@ d16~136@) (Mul b16~132@ c16~134@))))) (=> (= temp_16_1~2842@ (Add (Mul (Add (Mul c16~134@ d16~136@) (Mul c16~134@ c16~134@)) (Add (Mul b16~132@ 79) (Mul c16~134@ a16~130@))) (Mul (Sub (Mul b16~132@ a16~130@) (Sub 18 b16~132@)) (Mul (Mul a16~130@ d16~136@) (Mul b16~132@ c16~134@))))) (and (=> (ens%main!nl_basics.lemma_mul_properties_auto_1. 0) (=> %%location_label%%16 (= temp_16_0~2753@ temp_16_1~2842@))) (=> (= temp_16_0~2753@ temp_16_1~2842@) (=> (= temp_17_0~2923@ (Mul (Mul (Mul b17~140@ (Mul d17~144@ b17~140@)) (Add b17~140@ (Mul b17~140@ a17~138@))) (Mul (Add (Sub b17~140@ d17~144@) (Add c17~142@ b17~140@)) (Mul (Add c17~142@ a17~138@) (Mul c17~142@ b17~140@))))) (=> (= temp_17_1~2980@ (Mul (Mul (Mul b17~140@ (Mul b17~140@ d17~144@)) (Add b17~140@ (Mul b17~140@ a17~138@))) (Mul (Add (Sub b17~140@ d17~144@) (Add c17~142@ b17~140@)) (Mul (Add c17~142@ a17~138@) (Mul c17~142@ b17~140@))))) (and (=> (ens%main!nl_basics.lemma_mul_properties_auto_1. 0) (=> %%location_label%%17 (= temp_17_0~2923@ temp_17_1~2980@))) (=> (= temp_17_0~2923@ temp_17_1~2980@) (=> (= temp_18_0~3069@ (Mul (Add (Mul (Mul b18~148@ d18~152@) (Mul d18~152@ c18~150@)) (Add (Mul c18~150@ d18~152@) (Sub b18~148@ d18~152@))) (Add (Mul (Mul a18~146@ a18~146@) (Mul c18~150@ a18~146@)) (Mul (Mul a18~146@ b18~148@) (Mul d18~152@ c18~150@))))) (=> (= temp_18_1~3134@ (Mul (Add (Mul (Mul (Mul b18~148@ d18~152@) d18~152@) c18~150@) (Add (Mul c18~150@ d18~152@) (Sub b18~148@ d18~152@))) (Add (Mul (Mul a18~146@ a18~146@) (Mul c18~150@ a18~146@)) (Mul (Mul a18~146@ b18~148@) (Mul d18~152@ c18~150@))))) (and (=> (ens%main!nl_basics.lemma_mul_properties_auto_1. 0) (=> %%location_label%%18 (= temp_18_0~3069@ temp_18_1~3134@))) (=> (= temp_18_0~3069@ temp_18_1~3134@) (=> (= temp_19_0~3219@ (Sub (Mul (Mul b19~156@ (Mul b19~156@ c19~158@)) (Mul (Mul c19~158@ c19~158@) (Mul a19~154@ c19~158@))) (Mul (Mul (Mul d19~160@ c19~158@) (Mul d19~160@ a19~154@)) (Mul (Mul d19~160@ b19~156@) (Sub d19~160@ b19~156@))))) (=> (= temp_19_1~3280@ (Sub (Mul (Mul b19~156@ (Mul b19~156@ c19~158@)) (Mul (Mul c19~158@ c19~158@) (Mul a19~154@ c19~158@))) (Mul (Mul (Mul d19~160@ c19~158@) (Mul d19~160@ a19~154@)) (Mul (Sub d19~160@ b19~156@) (Mul d19~160@ b19~156@))))) (and (=> (ens%main!nl_basics.lemma_mul_properties_auto_1. 0) (=> %%location_label%%19 (= temp_19_0~3219@ temp_19_1~3280@))) (=> (= temp_19_0~3219@ temp_19_1~3280@) (=> (= temp_20_0~3377@ (Mul (Mul (Mul (Mul c20~166@ c20~166@) (Mul b20~164@ a20~162@)) (Mul (Mul 35 b20~164@) (Mul a20~162@ b20~164@))) (Mul (Mul (Mul b20~164@ b20~164@) (Mul a20~162@ a20~162@)) (Sub (Mul b20~164@ a20~162@) b20~164@)))) (=> (= temp_20_1~3450@ (Mul (Mul (Mul (Mul c20~166@ c20~166@) (Mul b20~164@ a20~162@)) (Mul (Mul 35 b20~164@) (Mul a20~162@ b20~164@))) (Mul (Mul (Mul b20~164@ b20~164@) (Mul a20~162@ a20~162@)) (Sub (Mul b20~164@ a20~162@) b20~164@)))) (and (=> (ens%main!nl_basics.lemma_mul_properties_auto_1. 0) (=> %%location_label%%20 (= temp_20_0~3377@ temp_20_1~3450@))) (=> (= temp_20_0~3377@ temp_20_1~3450@) (=> (= temp_21_0~3551@ (Mul (Mul (Mul (Mul b21~172@ b21~172@) (Mul d21~176@ b21~172@)) (Mul (Mul d21~176@ a21~170@) (Mul c21~174@ d21~176@))) (Mul (Mul (Mul b21~172@ 42) (Sub c21~174@ c21~174@)) (Add (Mul a21~170@ c21~174@) (Sub b21~172@ d21~176@))))) (=> (= temp_21_1~3656@ (Mul (Mul (Mul (Mul b21~172@ b21~172@) (Mul d21~176@ b21~172@)) (Mul (Mul d21~176@ a21~170@) (Mul c21~174@ d21~176@))) (Add (Mul (Mul (Mul b21~172@ 42) (Sub c21~174@ c21~174@)) (Mul a21~170@ c21~174@)) (Mul (Mul (Mul b21~172@ 42) (Sub c21~174@ c21~174@)) (Sub b21~172@ d21~176@))))) (and (=> (ens%main!nl_basics.lemma_mul_properties_auto_1. 0) (=> %%location_label%%21 (= temp_21_0~3551@ temp_21_1~3656@))) (=> (= temp_21_0~3551@ temp_21_1~3656@) (=> (= temp_22_0~3745@ (Mul (Mul (Mul (Sub c22~182@ c22~182@) (Mul b22~180@ c22~182@)) (Mul (Mul a22~178@ c22~182@) (Mul b22~180@ a22~178@))) (Mul (Mul (Mul c22~182@ b22~180@) (Mul b22~180@ d22~184@)) (Add (Mul d22~184@ d22~184@) (Mul c22~182@ d22~184@))))) (=> (= temp_22_1~3810@ (Mul (Mul (Mul (Mul b22~180@ c22~182@) (Sub c22~182@ c22~182@)) (Mul (Mul a22~178@ c22~182@) (Mul b22~180@ a22~178@))) (Mul (Mul (Mul c22~182@ b22~180@) (Mul b22~180@ d22~184@)) (Add (Mul d22~184@ d22~184@) (Mul c22~182@ d22~184@))))) (and (=> (ens%main!nl_basics.lemma_mul_properties_auto_1. 0) (=> %%location_label%%22 (= temp_22_0~3745@ temp_22_1~3810@))) (=> (= temp_22_0~3745@ temp_22_1~3810@) (=> (= temp_23_0~3895@ (Mul (Mul (Mul (Mul b23~188@ b23~188@) (Mul c23~190@ a23~186@)) (Mul (Mul b23~188@ c23~190@) d23~192@)) (Add (Mul (Sub d23~192@ a23~186@) (Mul a23~186@ b23~188@)) (Add (Sub c23~190@ d23~192@) (Add a23~186@ b23~188@))))) (=> (= temp_23_1~3956@ (Mul (Mul (Mul (Mul b23~188@ b23~188@) (Mul c23~190@ a23~186@)) (Mul (Mul b23~188@ c23~190@) d23~192@)) (Add (Mul (Mul a23~186@ b23~188@) (Sub d23~192@ a23~186@)) (Add (Sub c23~190@ d23~192@) (Add a23~186@ b23~188@))))) (=> (ens%main!nl_basics.lemma_mul_properties_auto_1. 0) (=> %%location_label%%23 (= temp_23_0~3895@ temp_23_1~3956@))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(assert %%query%%)
(check-sat)
