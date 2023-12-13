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
(set-info :comment ";; Function-Specs main::nl_basics::lemma_mul_is_associative")
(declare-fun ens%main!nl_basics.lemma_mul_is_associative. (Int Int Int) Bool)
(assert (forall ((x~2@ Int) (y~4@ Int) (z~6@ Int)) (! (= (ens%main!nl_basics.lemma_mul_is_associative. x~2@ y~4@ z~6@) (= (Mul x~2@ (Mul y~4@ z~6@)) (Mul (Mul x~2@ y~4@) z~6@))) :pattern ((ens%main!nl_basics.lemma_mul_is_associative. x~2@ y~4@ z~6@)) :qid internal_ens__main!nl_basics.lemma_mul_is_associative._definition :skolemid skolem_internal_ens__main!nl_basics.lemma_mul_is_associative._definition)))
(set-info :comment ";; Function-Specs main::nl_basics::lemma_mul_is_commutative")
(declare-fun ens%main!nl_basics.lemma_mul_is_commutative. (Int Int) Bool)
(assert (forall ((x~2@ Int) (y~4@ Int)) (! (= (ens%main!nl_basics.lemma_mul_is_commutative. x~2@ y~4@) (= (Mul x~2@ y~4@) (Mul y~4@ x~2@))) :pattern ((ens%main!nl_basics.lemma_mul_is_commutative. x~2@ y~4@)) :qid internal_ens__main!nl_basics.lemma_mul_is_commutative._definition :skolemid skolem_internal_ens__main!nl_basics.lemma_mul_is_commutative._definition)))
(set-info :comment ";; Function-Def main::inst_0")
(set-info :comment ";; mariposa_data/4//16167136263009972518/nlqi_verus/src/main.rs:7:1: 16:36 (#0)")
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
(declare-const tmp%1@ Int)
(declare-const tmp%2@ Int)
(declare-const tmp%3@ Int)
(declare-const tmp%4@ Int)
(declare-const tmp%5@ Int)
(declare-const tmp%6@ Int)
(declare-const temp_0_0~145@ Int)
(declare-const temp_0_1~210@ Int)
(declare-const temp_1_0~305@ Int)
(declare-const temp_1_1~366@ Int)
(declare-const temp_2_0~471@ Int)
(declare-const temp_2_1~548@ Int)
(declare-const temp_3_0~645@ Int)
(declare-const temp_3_1~706@ Int)
(declare-const temp_4_0~819@ Int)
(declare-const temp_4_1~884@ Int)
(declare-const temp_5_0~989@ Int)
(declare-const temp_5_1~1066@ Int)
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
(declare-const %%query%% Bool)
(assert (=> %%query%% (not (=> (= temp_0_0~145@ (Mul (Add (Mul (Mul a0~2@ a0~2@) (Mul a0~2@ b0~4@)) (Mul (Mul d0~8@ a0~2@) (Mul c0~6@ c0~6@))) (Mul (Mul (Mul b0~4@ c0~6@) (Add d0~8@ b0~4@)) (Mul (Mul a0~2@ a0~2@) (Mul c0~6@ b0~4@))))) (=> (= temp_0_1~210@ (Mul (Add (Mul (Mul a0~2@ a0~2@) (Mul a0~2@ b0~4@)) (Mul d0~8@ (Mul a0~2@ (Mul c0~6@ c0~6@)))) (Mul (Mul (Mul b0~4@ c0~6@) (Add d0~8@ b0~4@)) (Mul (Mul a0~2@ a0~2@) (Mul c0~6@ b0~4@))))) (and (=> (= tmp%1@ (Mul c0~6@ c0~6@)) (=> (ens%main!nl_basics.lemma_mul_is_associative. d0~8@ a0~2@ tmp%1@) (=> %%location_label%%0 (= temp_0_0~145@ temp_0_1~210@)))) (=> (= temp_0_0~145@ temp_0_1~210@) (=> (= temp_1_0~305@ (Mul (Mul (Mul (Mul d1~16@ d1~16@) (Mul b1~12@ c1~14@)) (Mul (Mul d1~16@ d1~16@) (Add a1~10@ a1~10@))) (Add (Mul (Mul a1~10@ a1~10@) (Mul d1~16@ a1~10@)) (Mul c1~14@ (Mul d1~16@ d1~16@))))) (=> (= temp_1_1~366@ (Mul (Mul (Mul (Mul d1~16@ d1~16@) (Mul b1~12@ c1~14@)) (Mul (Mul d1~16@ d1~16@) (Add a1~10@ a1~10@))) (Add (Mul (Mul a1~10@ a1~10@) (Mul d1~16@ a1~10@)) (Mul c1~14@ (Mul d1~16@ d1~16@))))) (and (=> (ens%main!nl_basics.lemma_mul_is_commutative. d1~16@ d1~16@) (=> %%location_label%%1 (= temp_1_0~305@ temp_1_1~366@))) (=> (= temp_1_0~305@ temp_1_1~366@) (=> (= temp_2_0~471@ (Mul (Mul (Mul (Mul b2~20@ c2~22@) (Mul b2~20@ 10)) (Mul (Add b2~20@ b2~20@) (Mul a2~18@ b2~20@))) (Mul (Mul (Mul a2~18@ d2~24@) (Mul a2~18@ c2~22@)) (Mul (Mul a2~18@ d2~24@) (Mul b2~20@ c2~22@))))) (=> (= temp_2_1~548@ (Mul (Mul (Mul (Mul b2~20@ c2~22@) (Mul b2~20@ 10)) (Mul (Mul a2~18@ b2~20@) (Add b2~20@ b2~20@))) (Mul (Mul (Mul a2~18@ d2~24@) (Mul a2~18@ c2~22@)) (Mul (Mul a2~18@ d2~24@) (Mul b2~20@ c2~22@))))) (and (=> (= tmp%2@ (Add b2~20@ b2~20@)) (=> (= tmp%3@ (Mul a2~18@ b2~20@)) (=> (ens%main!nl_basics.lemma_mul_is_commutative. tmp%2@ tmp%3@) (=> %%location_label%%2 (= temp_2_0~471@ temp_2_1~548@))))) (=> (= temp_2_0~471@ temp_2_1~548@) (=> (= temp_3_0~645@ (Add (Mul (Mul (Mul a3~26@ c3~30@) (Mul b3~28@ c3~30@)) (Mul (Mul d3~32@ d3~32@) (Mul c3~30@ b3~28@))) (Mul (Mul (Mul c3~30@ d3~32@) (Mul b3~28@ d3~32@)) (Mul b3~28@ (Mul b3~28@ a3~26@))))) (=> (= temp_3_1~706@ (Add (Mul (Mul (Mul a3~26@ c3~30@) (Mul b3~28@ c3~30@)) (Mul (Mul d3~32@ d3~32@) (Mul c3~30@ b3~28@))) (Mul (Mul b3~28@ (Mul b3~28@ a3~26@)) (Mul (Mul c3~30@ d3~32@) (Mul b3~28@ d3~32@))))) (and (=> (= tmp%4@ (Mul (Mul c3~30@ d3~32@) (Mul b3~28@ d3~32@))) (=> (= tmp%5@ (Mul b3~28@ (Mul b3~28@ a3~26@))) (=> (ens%main!nl_basics.lemma_mul_is_commutative. tmp%4@ tmp%5@) (=> %%location_label%%3 (= temp_3_0~645@ temp_3_1~706@))))) (=> (= temp_3_0~645@ temp_3_1~706@) (=> (= temp_4_0~819@ (Sub (Mul (Mul (Mul b4~36@ d4~40@) (Mul a4~34@ b4~36@)) (Mul (Mul b4~36@ c4~38@) (Add a4~34@ b4~36@))) (Sub (Mul (Mul a4~34@ a4~34@) (Add c4~38@ d4~40@)) (Mul (Mul c4~38@ a4~34@) (Mul d4~40@ a4~34@))))) (=> (= temp_4_1~884@ (Sub (Mul (Mul (Mul b4~36@ d4~40@) (Mul a4~34@ b4~36@)) (Mul (Mul b4~36@ c4~38@) (Add a4~34@ b4~36@))) (Sub (Mul (Mul a4~34@ a4~34@) (Add c4~38@ d4~40@)) (Mul (Mul c4~38@ a4~34@) (Mul d4~40@ a4~34@))))) (and (=> (ens%main!nl_basics.lemma_mul_is_commutative. a4~34@ a4~34@) (=> %%location_label%%4 (= temp_4_0~819@ temp_4_1~884@))) (=> (= temp_4_0~819@ temp_4_1~884@) (=> (= temp_5_0~989@ (Mul (Mul (Mul (Add a5~42@ b5~44@) (Mul c5~46@ d5~48@)) (Mul (Mul d5~48@ b5~44@) (Mul a5~42@ a5~42@))) (Mul (Mul (Mul d5~48@ b5~44@) (Mul d5~48@ c5~46@)) (Mul (Mul a5~42@ d5~48@) (Mul a5~42@ 4))))) (=> (= temp_5_1~1066@ (Mul (Mul (Mul (Add a5~42@ b5~44@) (Mul c5~46@ d5~48@)) (Mul (Mul (Mul d5~48@ b5~44@) a5~42@) a5~42@)) (Mul (Mul (Mul d5~48@ b5~44@) (Mul d5~48@ c5~46@)) (Mul (Mul a5~42@ d5~48@) (Mul a5~42@ 4))))) (=> (= tmp%6@ (Mul d5~48@ b5~44@)) (=> (ens%main!nl_basics.lemma_mul_is_associative. tmp%6@ a5~42@ a5~42@) (=> %%location_label%%5 (= temp_5_0~989@ temp_5_1~1066@)))))))))))))))))))))))))))))
(assert %%query%%)
(check-sat)
