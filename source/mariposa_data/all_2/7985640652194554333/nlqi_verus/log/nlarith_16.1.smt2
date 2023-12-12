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
(set-info :comment ";; mariposa_data/all_2//7985640652194554333/nlqi_verus/src/main.rs:7:1: 26:40 (#0)")
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
(set-info :comment ";; Function-Def main::nlarith_0")
(set-info :comment ";; mariposa_data/all_2//7985640652194554333/nlqi_verus/src/main.rs:7:1: 26:40 (#0)")
(set-option :smt.arith.solver 6)
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
(declare-const tmp%1@ Bool)
(declare-const tmp%2@ Bool)
(declare-const tmp%3@ Bool)
(declare-const tmp%4@ Bool)
(declare-const tmp%5@ Bool)
(declare-const tmp%6@ Bool)
(declare-const tmp%7@ Bool)
(declare-const tmp%8@ Bool)
(declare-const tmp%9@ Bool)
(declare-const tmp%10@ Bool)
(declare-const tmp%11@ Bool)
(declare-const tmp%12@ Bool)
(declare-const tmp%13@ Bool)
(declare-const tmp%14@ Bool)
(declare-const tmp%15@ Bool)
(declare-const tmp%16@ Bool)
(declare-const temp_0_0~177@ Int)
(declare-const temp_0_1~194@ Int)
(declare-const temp_1_0~226@ Int)
(declare-const temp_1_1~243@ Int)
(declare-const temp_2_0~275@ Int)
(declare-const temp_2_1~292@ Int)
(declare-const temp_3_0~324@ Int)
(declare-const temp_3_1~341@ Int)
(declare-const temp_4_0~373@ Int)
(declare-const temp_4_1~390@ Int)
(declare-const temp_5_0~422@ Int)
(declare-const temp_5_1~439@ Int)
(declare-const temp_6_0~483@ Int)
(declare-const temp_6_1~512@ Int)
(declare-const temp_7_0~544@ Int)
(declare-const temp_7_1~561@ Int)
(declare-const temp_8_0~605@ Int)
(declare-const temp_8_1~634@ Int)
(declare-const temp_9_0~666@ Int)
(declare-const temp_9_1~683@ Int)
(declare-const temp_10_0~715@ Int)
(declare-const temp_10_1~732@ Int)
(declare-const temp_11_0~764@ Int)
(declare-const temp_11_1~781@ Int)
(declare-const temp_12_0~813@ Int)
(declare-const temp_12_1~830@ Int)
(declare-const temp_13_0~862@ Int)
(declare-const temp_13_1~879@ Int)
(declare-const temp_14_0~911@ Int)
(declare-const temp_14_1~928@ Int)
(declare-const temp_15_0~960@ Int)
(declare-const temp_15_1~973@ Int)
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
(declare-const %%query%% Bool)
(assert (=> %%query%% (not (=> (= temp_0_0~177@ (Add (Mul d0~8@ c0~6@) (Mul a0~2@ b0~4@))) (=> (= temp_0_1~194@ (Add (Mul d0~8@ c0~6@) (Mul b0~4@ a0~2@))) (=> (= tmp%1@ (= temp_0_0~177@ temp_0_1~194@)) (and (=> %%location_label%%0 tmp%1@) (=> tmp%1@ (=> (= temp_1_0~226@ (Mul (Mul c1~14@ d1~16@) (Add d1~16@ a1~10@))) (=> (= temp_1_1~243@ (Mul (Mul d1~16@ c1~14@) (Add d1~16@ a1~10@))) (=> (= tmp%2@ (= temp_1_0~226@ temp_1_1~243@)) (and (=> %%location_label%%1 tmp%2@) (=> tmp%2@ (=> (= temp_2_0~275@ (Mul (Mul b2~20@ a2~18@) (Sub a2~18@ a2~18@))) (=> (= temp_2_1~292@ (Mul (Mul a2~18@ b2~20@) (Sub a2~18@ a2~18@))) (=> (= tmp%3@ (= temp_2_0~275@ temp_2_1~292@)) (and (=> %%location_label%%2 tmp%3@) (=> tmp%3@ (=> (= temp_3_0~324@ (Add (Mul a3~26@ c3~30@) (Mul c3~30@ d3~32@))) (=> (= temp_3_1~341@ (Add (Mul c3~30@ a3~26@) (Mul c3~30@ d3~32@))) (=> (= tmp%4@ (= temp_3_0~324@ temp_3_1~341@)) (and (=> %%location_label%%3 tmp%4@) (=> tmp%4@ (=> (= temp_4_0~373@ (Mul (Mul a4~34@ d4~40@) (Mul a4~34@ a4~34@))) (=> (= temp_4_1~390@ (Mul (Mul d4~40@ a4~34@) (Mul a4~34@ a4~34@))) (=> (= tmp%5@ (= temp_4_0~373@ temp_4_1~390@)) (and (=> %%location_label%%4 tmp%5@) (=> tmp%5@ (=> (= temp_5_0~422@ (Sub (Mul a5~42@ c5~46@) (Mul d5~48@ c5~46@))) (=> (= temp_5_1~439@ (Sub (Mul a5~42@ c5~46@) (Mul c5~46@ d5~48@))) (=> (= tmp%6@ (= temp_5_0~422@ temp_5_1~439@)) (and (=> %%location_label%%5 tmp%6@) (=> tmp%6@ (=> (= temp_6_0~483@ (Mul (Mul b6~52@ c6~54@) (Mul d6~56@ 99))) (=> (= temp_6_1~512@ (Mul (Mul d6~56@ 99) (Mul b6~52@ c6~54@))) (=> (= tmp%7@ (= temp_6_0~483@ temp_6_1~512@)) (and (=> %%location_label%%6 tmp%7@) (=> tmp%7@ (=> (= temp_7_0~544@ (Add (Mul c7~62@ a7~58@) (Mul b7~60@ c7~62@))) (=> (= temp_7_1~561@ (Add (Mul c7~62@ a7~58@) (Mul c7~62@ b7~60@))) (=> (= tmp%8@ (= temp_7_0~544@ temp_7_1~561@)) (and (=> %%location_label%%7 tmp%8@) (=> tmp%8@ (=> (= temp_8_0~605@ (Mul (Mul 50 d8~72@) (Mul a8~66@ d8~72@))) (=> (= temp_8_1~634@ (Mul (Mul d8~72@ 50) (Mul a8~66@ d8~72@))) (=> (= tmp%9@ (= temp_8_0~605@ temp_8_1~634@)) (and (=> %%location_label%%8 tmp%9@) (=> tmp%9@ (=> (= temp_9_0~666@ (Mul (Mul d9~80@ c9~78@) (Sub b9~76@ c9~78@))) (=> (= temp_9_1~683@ (Mul d9~80@ (Mul c9~78@ (Sub b9~76@ c9~78@)))) (=> (= tmp%10@ (= temp_9_0~666@ temp_9_1~683@)) (and (=> %%location_label%%9 tmp%10@) (=> tmp%10@ (=> (= temp_10_0~715@ (Mul (Mul d10~88@ c10~86@) (Mul a10~82@ c10~86@))) (=> (= temp_10_1~732@ (Mul (Mul d10~88@ c10~86@) (Mul c10~86@ a10~82@))) (=> (= tmp%11@ (= temp_10_0~715@ temp_10_1~732@)) (and (=> %%location_label%%10 tmp%11@) (=> tmp%11@ (=> (= temp_11_0~764@ (Mul (Mul d11~96@ d11~96@) (Sub a11~90@ c11~94@))) (=> (= temp_11_1~781@ (Mul (Sub a11~90@ c11~94@) (Mul d11~96@ d11~96@))) (=> (= tmp%12@ (= temp_11_0~764@ temp_11_1~781@)) (and (=> %%location_label%%11 tmp%12@) (=> tmp%12@ (=> (= temp_12_0~813@ (Add (Mul c12~102@ b12~100@) (Add d12~104@ a12~98@))) (=> (= temp_12_1~830@ (Add (Mul b12~100@ c12~102@) (Add d12~104@ a12~98@))) (=> (= tmp%13@ (= temp_12_0~813@ temp_12_1~830@)) (and (=> %%location_label%%12 tmp%13@) (=> tmp%13@ (=> (= temp_13_0~862@ (Mul (Mul a13~106@ b13~108@) (Mul a13~106@ d13~112@))) (=> (= temp_13_1~879@ (Mul (Mul (Mul a13~106@ b13~108@) a13~106@) d13~112@)) (=> (= tmp%14@ (= temp_13_0~862@ temp_13_1~879@)) (and (=> %%location_label%%13 tmp%14@) (=> tmp%14@ (=> (= temp_14_0~911@ (Mul (Mul b14~116@ d14~120@) (Mul c14~118@ b14~116@))) (=> (= temp_14_1~928@ (Mul (Mul (Mul b14~116@ d14~120@) c14~118@) b14~116@)) (=> (= tmp%15@ (= temp_14_0~911@ temp_14_1~928@)) (and (=> %%location_label%%14 tmp%15@) (=> tmp%15@ (=> (= temp_15_0~960@ (Add (Mul d15~128@ b15~124@) (Mul d15~128@ a15~122@))) (=> (= temp_15_1~973@ (Mul d15~128@ (Add b15~124@ a15~122@))) (=> (= tmp%16@ (= temp_15_0~960@ temp_15_1~973@)) (=> %%location_label%%15 tmp%16@))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(assert %%query%%)
(check-sat)
