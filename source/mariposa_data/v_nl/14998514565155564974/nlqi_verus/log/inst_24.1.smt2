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
(set-info :comment ";; Function-Specs main::nl_basics::lemma_mul_is_distributive")
(declare-fun ens%main!nl_basics.lemma_mul_is_distributive. (Int Int Int) Bool)
(assert (forall ((x~2@ Int) (y~4@ Int) (z~6@ Int)) (! (= (ens%main!nl_basics.lemma_mul_is_distributive. x~2@ y~4@ z~6@) (and (= (Mul x~2@ (Add y~4@ z~6@)) (Add (Mul x~2@ y~4@) (Mul x~2@ z~6@))) (= (Mul (Add x~2@ y~4@) z~6@) (Add (Mul x~2@ z~6@) (Mul y~4@ z~6@))) (= (Mul x~2@ (Sub y~4@ z~6@)) (Sub (Mul x~2@ y~4@) (Mul x~2@ z~6@))) (= (Mul (Sub x~2@ y~4@) z~6@) (Sub (Mul x~2@ z~6@) (Mul y~4@ z~6@))))) :pattern ((ens%main!nl_basics.lemma_mul_is_distributive. x~2@ y~4@ z~6@)) :qid internal_ens__main!nl_basics.lemma_mul_is_distributive._definition :skolemid skolem_internal_ens__main!nl_basics.lemma_mul_is_distributive._definition)))
(set-info :comment ";; Function-Def main::inst_0")
(set-info :comment ";; mariposa_data/v_nl//14998514565155564974/nlqi_verus/src/main.rs:7:1: 36:40 (#0)")
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
(declare-const tmp%1@ Int)
(declare-const tmp%2@ Int)
(declare-const tmp%3@ Int)
(declare-const tmp%4@ Int)
(declare-const tmp%5@ Int)
(declare-const tmp%6@ Int)
(declare-const tmp%7@ Int)
(declare-const tmp%8@ Int)
(declare-const tmp%9@ Int)
(declare-const tmp%10@ Int)
(declare-const tmp%11@ Int)
(declare-const tmp%12@ Int)
(declare-const tmp%13@ Int)
(declare-const tmp%14@ Int)
(declare-const tmp%15@ Int)
(declare-const tmp%16@ Int)
(declare-const tmp%17@ Int)
(declare-const tmp%18@ Int)
(declare-const tmp%19@ Int)
(declare-const tmp%20@ Int)
(declare-const tmp%21@ Int)
(declare-const tmp%22@ Int)
(declare-const tmp%23@ Int)
(declare-const tmp%24@ Int)
(declare-const tmp%25@ Int)
(declare-const tmp%26@ Int)
(declare-const temp_0_0~297@ Int)
(declare-const temp_0_1~350@ Int)
(declare-const temp_1_0~445@ Int)
(declare-const temp_1_1~510@ Int)
(declare-const temp_2_0~619@ Int)
(declare-const temp_2_1~692@ Int)
(declare-const temp_3_0~817@ Int)
(declare-const temp_3_1~894@ Int)
(declare-const temp_4_0~979@ Int)
(declare-const temp_4_1~1036@ Int)
(declare-const temp_5_0~1137@ Int)
(declare-const temp_5_1~1210@ Int)
(declare-const temp_6_0~1295@ Int)
(declare-const temp_6_1~1352@ Int)
(declare-const temp_7_0~1455@ Int)
(declare-const temp_7_1~1508@ Int)
(declare-const temp_8_0~1645@ Int)
(declare-const temp_8_1~1710@ Int)
(declare-const temp_9_0~1775@ Int)
(declare-const temp_9_1~1812@ Int)
(declare-const temp_10_0~1925@ Int)
(declare-const temp_10_1~2030@ Int)
(declare-const temp_11_0~2137@ Int)
(declare-const temp_11_1~2230@ Int)
(declare-const temp_12_0~2373@ Int)
(declare-const temp_12_1~2438@ Int)
(declare-const temp_13_0~2535@ Int)
(declare-const temp_13_1~2596@ Int)
(declare-const temp_14_0~2679@ Int)
(declare-const temp_14_1~2736@ Int)
(declare-const temp_15_0~2835@ Int)
(declare-const temp_15_1~2900@ Int)
(declare-const temp_16_0~2989@ Int)
(declare-const temp_16_1~3038@ Int)
(declare-const temp_17_0~3145@ Int)
(declare-const temp_17_1~3222@ Int)
(declare-const temp_18_0~3307@ Int)
(declare-const temp_18_1~3364@ Int)
(declare-const temp_19_0~3445@ Int)
(declare-const temp_19_1~3498@ Int)
(declare-const temp_20_0~3585@ Int)
(declare-const temp_20_1~3642@ Int)
(declare-const temp_21_0~3733@ Int)
(declare-const temp_21_1~3786@ Int)
(declare-const temp_22_0~3931@ Int)
(declare-const temp_22_1~4004@ Int)
(declare-const temp_23_0~4157@ Int)
(declare-const temp_23_1~4246@ Int)
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
(assert (=> %%query%% (not (=> (= temp_0_0~297@ (Mul (Mul (Mul (Add c0~6@ a0~2@) (Mul c0~6@ d0~8@)) (Sub (Mul b0~4@ b0~4@) (Mul b0~4@ a0~2@))) (Mul (Mul (Mul d0~8@ b0~4@) c0~6@) (Add (Mul a0~2@ d0~8@) b0~4@)))) (=> (= temp_0_1~350@ (Mul (Mul (Mul (Add c0~6@ a0~2@) (Mul c0~6@ d0~8@)) (Mul b0~4@ (Sub b0~4@ a0~2@))) (Mul (Mul (Mul d0~8@ b0~4@) c0~6@) (Add (Mul a0~2@ d0~8@) b0~4@)))) (and (=> (ens%main!nl_basics.lemma_mul_is_distributive. b0~4@ b0~4@ a0~2@) (=> %%location_label%%0 (= temp_0_0~297@ temp_0_1~350@))) (=> (= temp_0_0~297@ temp_0_1~350@) (=> (= temp_1_0~445@ (Add (Mul (Mul (Mul a1~10@ c1~14@) (Mul a1~10@ c1~14@)) (Mul (Add c1~14@ c1~14@) (Mul d1~16@ b1~12@))) (Mul (Sub (Mul a1~10@ d1~16@) (Mul b1~12@ a1~10@)) (Mul (Mul c1~14@ c1~14@) (Mul d1~16@ b1~12@))))) (=> (= temp_1_1~510@ (Add (Mul (Mul (Mul a1~10@ c1~14@) (Mul a1~10@ c1~14@)) (Mul (Add c1~14@ c1~14@) (Mul d1~16@ b1~12@))) (Mul (Sub (Mul a1~10@ d1~16@) (Mul b1~12@ a1~10@)) (Mul (Mul d1~16@ b1~12@) (Mul c1~14@ c1~14@))))) (and (=> (= tmp%1@ (Mul c1~14@ c1~14@)) (=> (= tmp%2@ (Mul d1~16@ b1~12@)) (=> (ens%main!nl_basics.lemma_mul_is_commutative. tmp%1@ tmp%2@) (=> %%location_label%%1 (= temp_1_0~445@ temp_1_1~510@))))) (=> (= temp_1_0~445@ temp_1_1~510@) (=> (= temp_2_0~619@ (Mul (Mul (Mul c2~22@ (Sub d2~24@ c2~22@)) (Mul (Mul a2~18@ c2~22@) (Mul a2~18@ c2~22@))) (Mul (Mul (Mul c2~22@ a2~18@) (Mul c2~22@ b2~20@)) (Mul (Mul c2~22@ d2~24@) (Mul d2~24@ 97))))) (=> (= temp_2_1~692@ (Mul (Mul (Mul (Mul a2~18@ c2~22@) (Mul a2~18@ c2~22@)) (Mul c2~22@ (Sub d2~24@ c2~22@))) (Mul (Mul (Mul c2~22@ a2~18@) (Mul c2~22@ b2~20@)) (Mul (Mul c2~22@ d2~24@) (Mul d2~24@ 97))))) (and (=> (= tmp%3@ (Mul c2~22@ (Sub d2~24@ c2~22@))) (=> (= tmp%4@ (Mul (Mul a2~18@ c2~22@) (Mul a2~18@ c2~22@))) (=> (ens%main!nl_basics.lemma_mul_is_commutative. tmp%3@ tmp%4@) (=> %%location_label%%2 (= temp_2_0~619@ temp_2_1~692@))))) (=> (= temp_2_0~619@ temp_2_1~692@) (=> (= temp_3_0~817@ (Mul (Mul (Mul (Mul b3~28@ b3~28@) (Mul a3~26@ 27)) (Mul (Mul a3~26@ b3~28@) (Mul d3~32@ d3~32@))) (Mul (Mul (Mul b3~28@ c3~30@) (Mul c3~30@ a3~26@)) (Add (Mul d3~32@ a3~26@) (Mul a3~26@ c3~30@))))) (=> (= temp_3_1~894@ (Mul (Mul (Mul (Mul b3~28@ b3~28@) (Mul a3~26@ 27)) (Mul (Mul a3~26@ b3~28@) (Mul d3~32@ d3~32@))) (Mul (Mul (Mul b3~28@ c3~30@) (Mul c3~30@ a3~26@)) (Add (Mul d3~32@ a3~26@) (Mul c3~30@ a3~26@))))) (and (=> (ens%main!nl_basics.lemma_mul_is_commutative. a3~26@ c3~30@) (=> %%location_label%%3 (= temp_3_0~817@ temp_3_1~894@))) (=> (= temp_3_0~817@ temp_3_1~894@) (=> (= temp_4_0~979@ (Mul (Mul (Sub (Mul b4~36@ b4~36@) a4~34@) (Mul (Add b4~36@ d4~40@) (Mul c4~38@ c4~38@))) (Add (Mul (Mul a4~34@ b4~36@) (Mul d4~40@ d4~40@)) (Mul a4~34@ (Mul c4~38@ d4~40@))))) (=> (= temp_4_1~1036@ (Mul (Mul (Sub (Mul b4~36@ b4~36@) a4~34@) (Mul (Add b4~36@ d4~40@) (Mul c4~38@ c4~38@))) (Add (Mul (Mul a4~34@ b4~36@) (Mul d4~40@ d4~40@)) (Mul a4~34@ (Mul d4~40@ c4~38@))))) (and (=> (ens%main!nl_basics.lemma_mul_is_commutative. c4~38@ d4~40@) (=> %%location_label%%4 (= temp_4_0~979@ temp_4_1~1036@))) (=> (= temp_4_0~979@ temp_4_1~1036@) (=> (= temp_5_0~1137@ (Mul (Sub (Mul a5~42@ (Sub 76 a5~42@)) (Add (Mul d5~48@ c5~46@) (Mul a5~42@ a5~42@))) (Mul (Mul (Mul c5~46@ c5~46@) (Mul d5~48@ c5~46@)) (Mul (Add c5~46@ c5~46@) (Mul b5~44@ d5~48@))))) (=> (= temp_5_1~1210@ (Mul (Sub (Mul a5~42@ (Sub 76 a5~42@)) (Add (Mul d5~48@ c5~46@) (Mul a5~42@ a5~42@))) (Mul (Mul (Mul c5~46@ c5~46@) (Mul c5~46@ d5~48@)) (Mul (Add c5~46@ c5~46@) (Mul b5~44@ d5~48@))))) (and (=> (ens%main!nl_basics.lemma_mul_is_commutative. d5~48@ c5~46@) (=> %%location_label%%5 (= temp_5_0~1137@ temp_5_1~1210@))) (=> (= temp_5_0~1137@ temp_5_1~1210@) (=> (= temp_6_0~1295@ (Mul (Mul (Mul (Mul a6~50@ d6~56@) (Mul b6~52@ d6~56@)) (Mul (Mul b6~52@ d6~56@) (Mul a6~50@ d6~56@))) (Mul (Mul b6~52@ (Add b6~52@ c6~54@)) (Mul (Sub d6~56@ c6~54@) b6~52@)))) (=> (= temp_6_1~1352@ (Mul (Mul (Mul (Mul (Mul a6~50@ d6~56@) (Mul b6~52@ d6~56@)) (Mul b6~52@ d6~56@)) (Mul a6~50@ d6~56@)) (Mul (Mul b6~52@ (Add b6~52@ c6~54@)) (Mul (Sub d6~56@ c6~54@) b6~52@)))) (and (=> (= tmp%5@ (Mul (Mul a6~50@ d6~56@) (Mul b6~52@ d6~56@))) (=> (= tmp%6@ (Mul b6~52@ d6~56@)) (=> (= tmp%7@ (Mul a6~50@ d6~56@)) (=> (ens%main!nl_basics.lemma_mul_is_associative. tmp%5@ tmp%6@ tmp%7@) (=> %%location_label%%6 (= temp_6_0~1295@ temp_6_1~1352@)))))) (=> (= temp_6_0~1295@ temp_6_1~1352@) (=> (= temp_7_0~1455@ (Mul (Mul (Mul (Add c7~62@ b7~60@) (Mul b7~60@ a7~58@)) a7~58@) (Mul (Sub (Mul a7~58@ a7~58@) (Mul b7~60@ d7~64@)) (Mul (Mul a7~58@ d7~64@) (Mul b7~60@ b7~60@))))) (=> (= temp_7_1~1508@ (Mul (Mul (Sub (Mul a7~58@ a7~58@) (Mul b7~60@ d7~64@)) (Mul (Mul a7~58@ d7~64@) (Mul b7~60@ b7~60@))) (Mul (Mul (Add c7~62@ b7~60@) (Mul b7~60@ a7~58@)) a7~58@))) (and (=> (= tmp%8@ (Mul (Mul (Add c7~62@ b7~60@) (Mul b7~60@ a7~58@)) a7~58@)) (=> (= tmp%9@ (Mul (Sub (Mul a7~58@ a7~58@) (Mul b7~60@ d7~64@)) (Mul (Mul a7~58@ d7~64@) (Mul b7~60@ b7~60@)))) (=> (ens%main!nl_basics.lemma_mul_is_commutative. tmp%8@ tmp%9@) (=> %%location_label%%7 (= temp_7_0~1455@ temp_7_1~1508@))))) (=> (= temp_7_0~1455@ temp_7_1~1508@) (=> (= temp_8_0~1645@ (Mul (Mul (Mul (Add c8~70@ a8~66@) (Sub d8~72@ c8~70@)) (Mul (Mul d8~72@ d8~72@) (Mul c8~70@ 91))) (Mul d8~72@ (Mul (Mul c8~70@ c8~70@) (Mul a8~66@ d8~72@))))) (=> (= temp_8_1~1710@ (Mul (Mul (Mul (Add c8~70@ a8~66@) (Sub d8~72@ c8~70@)) (Mul (Mul d8~72@ d8~72@) (Mul c8~70@ 91))) (Mul d8~72@ (Mul (Mul c8~70@ c8~70@) (Mul a8~66@ d8~72@))))) (and (=> (ens%main!nl_basics.lemma_mul_is_commutative. d8~72@ d8~72@) (=> %%location_label%%8 (= temp_8_0~1645@ temp_8_1~1710@))) (=> (= temp_8_0~1645@ temp_8_1~1710@) (=> (= temp_9_0~1775@ (Mul (Mul (Mul (Mul b9~76@ d9~80@) (Mul d9~80@ b9~76@)) (Mul c9~78@ (Sub a9~74@ b9~76@))) (Mul a9~74@ a9~74@))) (=> (= temp_9_1~1812@ (Mul (Mul (Mul (Mul d9~80@ b9~76@) (Mul d9~80@ b9~76@)) (Mul c9~78@ (Sub a9~74@ b9~76@))) (Mul a9~74@ a9~74@))) (and (=> (ens%main!nl_basics.lemma_mul_is_commutative. b9~76@ d9~80@) (=> %%location_label%%9 (= temp_9_0~1775@ temp_9_1~1812@))) (=> (= temp_9_0~1775@ temp_9_1~1812@) (=> (= temp_10_0~1925@ (Mul (Mul (Mul (Add d10~88@ d10~88@) (Mul 66 a10~82@)) (Mul (Mul 56 b10~84@) d10~88@)) (Mul (Mul (Mul b10~84@ d10~88@) (Mul c10~86@ b10~84@)) (Mul (Add d10~88@ c10~86@) (Mul d10~88@ c10~86@))))) (=> (= temp_10_1~2030@ (Mul (Mul (Add (Mul d10~88@ (Mul 66 a10~82@)) (Mul d10~88@ (Mul 66 a10~82@))) (Mul (Mul 56 b10~84@) d10~88@)) (Mul (Mul (Mul b10~84@ d10~88@) (Mul c10~86@ b10~84@)) (Mul (Add d10~88@ c10~86@) (Mul d10~88@ c10~86@))))) (and (=> (= tmp%10@ (Mul 66 a10~82@)) (=> (ens%main!nl_basics.lemma_mul_is_distributive. d10~88@ d10~88@ tmp%10@) (=> %%location_label%%10 (= temp_10_0~1925@ temp_10_1~2030@)))) (=> (= temp_10_0~1925@ temp_10_1~2030@) (=> (= temp_11_0~2137@ (Mul (Add (Mul (Mul b11~92@ a11~90@) (Mul b11~92@ b11~92@)) (Mul b11~92@ (Mul d11~96@ d11~96@))) (Mul (Add (Mul b11~92@ a11~90@) (Mul d11~96@ c11~94@)) (Mul (Mul b11~92@ d11~96@) (Mul d11~96@ d11~96@))))) (=> (= temp_11_1~2230@ (Add (Mul (Mul (Mul b11~92@ a11~90@) (Mul b11~92@ b11~92@)) (Mul (Add (Mul b11~92@ a11~90@) (Mul d11~96@ c11~94@)) (Mul (Mul b11~92@ d11~96@) (Mul d11~96@ d11~96@)))) (Mul (Mul b11~92@ (Mul d11~96@ d11~96@)) (Mul (Add (Mul b11~92@ a11~90@) (Mul d11~96@ c11~94@)) (Mul (Mul b11~92@ d11~96@) (Mul d11~96@ d11~96@)))))) (and (=> (= tmp%11@ (Mul (Mul b11~92@ a11~90@) (Mul b11~92@ b11~92@))) (=> (= tmp%12@ (Mul b11~92@ (Mul d11~96@ d11~96@))) (=> (= tmp%13@ (Mul (Add (Mul b11~92@ a11~90@) (Mul d11~96@ c11~94@)) (Mul (Mul b11~92@ d11~96@) (Mul d11~96@ d11~96@)))) (=> (ens%main!nl_basics.lemma_mul_is_distributive. tmp%11@ tmp%12@ tmp%13@) (=> %%location_label%%11 (= temp_11_0~2137@ temp_11_1~2230@)))))) (=> (= temp_11_0~2137@ temp_11_1~2230@) (=> (= temp_12_0~2373@ (Mul (Mul (Mul (Mul d12~104@ b12~100@) (Mul d12~104@ c12~102@)) (Mul (Mul c12~102@ a12~98@) (Mul a12~98@ c12~102@))) (Add (Mul (Mul c12~102@ a12~98@) (Mul b12~100@ a12~98@)) (Mul (Sub d12~104@ d12~104@) (Mul d12~104@ a12~98@))))) (=> (= temp_12_1~2438@ (Mul (Mul (Mul (Mul d12~104@ b12~100@) (Mul d12~104@ c12~102@)) (Mul (Mul a12~98@ c12~102@) (Mul c12~102@ a12~98@))) (Add (Mul (Mul c12~102@ a12~98@) (Mul b12~100@ a12~98@)) (Mul (Sub d12~104@ d12~104@) (Mul d12~104@ a12~98@))))) (and (=> (= tmp%14@ (Mul c12~102@ a12~98@)) (=> (= tmp%15@ (Mul a12~98@ c12~102@)) (=> (ens%main!nl_basics.lemma_mul_is_commutative. tmp%14@ tmp%15@) (=> %%location_label%%12 (= temp_12_0~2373@ temp_12_1~2438@))))) (=> (= temp_12_0~2373@ temp_12_1~2438@) (=> (= temp_13_0~2535@ (Mul (Mul (Mul (Mul c13~110@ a13~106@) (Mul b13~108@ b13~108@)) (Mul (Mul b13~108@ d13~112@) (Mul b13~108@ d13~112@))) (Mul (Mul (Mul d13~112@ b13~108@) (Mul c13~110@ c13~110@)) (Mul c13~110@ (Mul b13~108@ b13~108@))))) (=> (= temp_13_1~2596@ (Mul (Mul (Mul c13~110@ (Mul a13~106@ (Mul b13~108@ b13~108@))) (Mul (Mul b13~108@ d13~112@) (Mul b13~108@ d13~112@))) (Mul (Mul (Mul d13~112@ b13~108@) (Mul c13~110@ c13~110@)) (Mul c13~110@ (Mul b13~108@ b13~108@))))) (and (=> (= tmp%16@ (Mul b13~108@ b13~108@)) (=> (ens%main!nl_basics.lemma_mul_is_associative. c13~110@ a13~106@ tmp%16@) (=> %%location_label%%13 (= temp_13_0~2535@ temp_13_1~2596@)))) (=> (= temp_13_0~2535@ temp_13_1~2596@) (=> (= temp_14_0~2679@ (Mul (Mul (Mul (Sub c14~118@ b14~116@) (Add b14~116@ b14~116@)) (Mul (Mul d14~120@ a14~114@) (Add c14~118@ a14~114@))) 22)) (=> (= temp_14_1~2736@ (Mul (Mul (Mul (Sub c14~118@ b14~116@) (Add b14~116@ b14~116@)) (Add (Mul (Mul d14~120@ a14~114@) c14~118@) (Mul (Mul d14~120@ a14~114@) a14~114@))) 22)) (and (=> (= tmp%17@ (Mul d14~120@ a14~114@)) (=> (ens%main!nl_basics.lemma_mul_is_distributive. tmp%17@ c14~118@ a14~114@) (=> %%location_label%%14 (= temp_14_0~2679@ temp_14_1~2736@)))) (=> (= temp_14_0~2679@ temp_14_1~2736@) (=> (= temp_15_0~2835@ (Mul (Mul (Mul (Mul b15~124@ d15~128@) (Mul b15~124@ d15~128@)) (Mul (Mul a15~122@ b15~124@) (Add b15~124@ d15~128@))) (Mul (Mul (Sub b15~124@ c15~126@) (Mul a15~122@ b15~124@)) (Mul (Mul c15~126@ c15~126@) (Mul a15~122@ c15~126@))))) (=> (= temp_15_1~2900@ (Mul (Mul (Mul (Mul b15~124@ d15~128@) (Mul b15~124@ d15~128@)) (Mul (Mul a15~122@ b15~124@) (Add b15~124@ d15~128@))) (Mul (Mul (Sub b15~124@ c15~126@) (Mul a15~122@ b15~124@)) (Mul (Mul a15~122@ c15~126@) (Mul c15~126@ c15~126@))))) (and (=> (= tmp%18@ (Mul c15~126@ c15~126@)) (=> (= tmp%19@ (Mul a15~122@ c15~126@)) (=> (ens%main!nl_basics.lemma_mul_is_commutative. tmp%18@ tmp%19@) (=> %%location_label%%15 (= temp_15_0~2835@ temp_15_1~2900@))))) (=> (= temp_15_0~2835@ temp_15_1~2900@) (=> (= temp_16_0~2989@ (Mul (Mul (Sub (Mul a16~130@ b16~132@) (Mul a16~130@ d16~136@)) (Mul (Mul b16~132@ c16~134@) (Mul a16~130@ a16~130@))) (Mul (Mul (Mul a16~130@ c16~134@) (Mul a16~130@ b16~132@)) d16~136@))) (=> (= temp_16_1~3038@ (Mul (Mul (Mul a16~130@ (Sub b16~132@ d16~136@)) (Mul (Mul b16~132@ c16~134@) (Mul a16~130@ a16~130@))) (Mul (Mul (Mul a16~130@ c16~134@) (Mul a16~130@ b16~132@)) d16~136@))) (and (=> (ens%main!nl_basics.lemma_mul_is_distributive. a16~130@ b16~132@ d16~136@) (=> %%location_label%%16 (= temp_16_0~2989@ temp_16_1~3038@))) (=> (= temp_16_0~2989@ temp_16_1~3038@) (=> (= temp_17_0~3145@ (Mul (Add (Mul (Add b17~140@ c17~142@) (Mul 36 d17~144@)) (Mul (Mul b17~140@ a17~138@) (Mul d17~144@ d17~144@))) (Mul (Mul (Mul d17~144@ b17~140@) (Mul d17~144@ d17~144@)) (Mul (Mul d17~144@ c17~142@) (Sub c17~142@ b17~140@))))) (=> (= temp_17_1~3222@ (Mul (Add (Mul (Add b17~140@ c17~142@) (Mul 36 d17~144@)) (Mul (Mul b17~140@ a17~138@) (Mul d17~144@ d17~144@))) (Mul (Mul (Mul d17~144@ b17~140@) (Mul d17~144@ d17~144@)) (Mul (Mul d17~144@ c17~142@) (Sub c17~142@ b17~140@))))) (and (=> (ens%main!nl_basics.lemma_mul_is_commutative. d17~144@ d17~144@) (=> %%location_label%%17 (= temp_17_0~3145@ temp_17_1~3222@))) (=> (= temp_17_0~3145@ temp_17_1~3222@) (=> (= temp_18_0~3307@ (Mul (Mul (Sub (Mul c18~150@ b18~148@) (Mul b18~148@ c18~150@)) (Mul a18~146@ a18~146@)) (Mul (Sub (Mul b18~148@ d18~152@) (Mul d18~152@ b18~148@)) (Mul (Add b18~148@ a18~146@) (Mul d18~152@ c18~150@))))) (=> (= temp_18_1~3364@ (Mul (Mul (Sub (Mul c18~150@ b18~148@) (Mul b18~148@ c18~150@)) (Mul a18~146@ a18~146@)) (Mul (Sub (Mul d18~152@ b18~148@) (Mul d18~152@ b18~148@)) (Mul (Add b18~148@ a18~146@) (Mul d18~152@ c18~150@))))) (and (=> (ens%main!nl_basics.lemma_mul_is_commutative. b18~148@ d18~152@) (=> %%location_label%%18 (= temp_18_0~3307@ temp_18_1~3364@))) (=> (= temp_18_0~3307@ temp_18_1~3364@) (=> (= temp_19_0~3445@ (Mul (Mul d19~160@ (Mul (Mul d19~160@ d19~160@) (Mul b19~156@ d19~160@))) (Mul (Sub (Mul b19~156@ a19~154@) (Mul b19~156@ d19~160@)) (Mul (Add d19~160@ d19~160@) (Mul d19~160@ a19~154@))))) (=> (= temp_19_1~3498@ (Mul (Mul d19~160@ (Mul d19~160@ (Mul d19~160@ (Mul b19~156@ d19~160@)))) (Mul (Sub (Mul b19~156@ a19~154@) (Mul b19~156@ d19~160@)) (Mul (Add d19~160@ d19~160@) (Mul d19~160@ a19~154@))))) (and (=> (= tmp%20@ (Mul b19~156@ d19~160@)) (=> (ens%main!nl_basics.lemma_mul_is_associative. d19~160@ d19~160@ tmp%20@) (=> %%location_label%%19 (= temp_19_0~3445@ temp_19_1~3498@)))) (=> (= temp_19_0~3445@ temp_19_1~3498@) (=> (= temp_20_0~3585@ (Sub (Mul (Mul (Add c20~166@ b20~164@) (Mul a20~162@ a20~162@)) (Sub (Mul d20~168@ b20~164@) (Mul d20~168@ b20~164@))) (Mul b20~164@ (Add (Mul b20~164@ b20~164@) (Mul b20~164@ b20~164@))))) (=> (= temp_20_1~3642@ (Sub (Mul (Mul (Add c20~166@ b20~164@) (Mul a20~162@ a20~162@)) (Sub (Mul d20~168@ b20~164@) (Mul d20~168@ b20~164@))) (Add (Mul b20~164@ (Mul b20~164@ b20~164@)) (Mul b20~164@ (Mul b20~164@ b20~164@))))) (and (=> (= tmp%21@ (Mul b20~164@ b20~164@)) (=> (= tmp%22@ (Mul b20~164@ b20~164@)) (=> (ens%main!nl_basics.lemma_mul_is_distributive. b20~164@ tmp%21@ tmp%22@) (=> %%location_label%%20 (= temp_20_0~3585@ temp_20_1~3642@))))) (=> (= temp_20_0~3585@ temp_20_1~3642@) (=> (= temp_21_0~3733@ (Mul (Mul d21~176@ (Mul (Mul d21~176@ b21~172@) (Mul d21~176@ c21~174@))) (Mul (Sub (Mul b21~172@ b21~172@) (Sub a21~170@ c21~174@)) (Sub (Mul d21~176@ d21~176@) (Mul c21~174@ a21~170@))))) (=> (= temp_21_1~3786@ (Mul (Mul (Sub (Mul b21~172@ b21~172@) (Sub a21~170@ c21~174@)) (Sub (Mul d21~176@ d21~176@) (Mul c21~174@ a21~170@))) (Mul d21~176@ (Mul (Mul d21~176@ b21~172@) (Mul d21~176@ c21~174@))))) (and (=> (= tmp%23@ (Mul d21~176@ (Mul (Mul d21~176@ b21~172@) (Mul d21~176@ c21~174@)))) (=> (= tmp%24@ (Mul (Sub (Mul b21~172@ b21~172@) (Sub a21~170@ c21~174@)) (Sub (Mul d21~176@ d21~176@) (Mul c21~174@ a21~170@)))) (=> (ens%main!nl_basics.lemma_mul_is_commutative. tmp%23@ tmp%24@) (=> %%location_label%%21 (= temp_21_0~3733@ temp_21_1~3786@))))) (=> (= temp_21_0~3733@ temp_21_1~3786@) (=> (= temp_22_0~3931@ (Mul (Mul (Mul (Mul a22~178@ b22~180@) (Add a22~178@ c22~182@)) (Mul b22~180@ (Mul d22~184@ d22~184@))) (Mul (Mul (Mul b22~180@ b22~180@) (Mul 13 d22~184@)) (Mul (Mul d22~184@ d22~184@) (Mul a22~178@ b22~180@))))) (=> (= temp_22_1~4004@ (Mul (Mul (Mul (Mul a22~178@ b22~180@) (Add a22~178@ c22~182@)) (Mul b22~180@ (Mul d22~184@ d22~184@))) (Mul (Mul (Mul d22~184@ d22~184@) (Mul a22~178@ b22~180@)) (Mul (Mul b22~180@ b22~180@) (Mul 13 d22~184@))))) (and (=> (= tmp%25@ (Mul (Mul b22~180@ b22~180@) (Mul 13 d22~184@))) (=> (= tmp%26@ (Mul (Mul d22~184@ d22~184@) (Mul a22~178@ b22~180@))) (=> (ens%main!nl_basics.lemma_mul_is_commutative. tmp%25@ tmp%26@) (=> %%location_label%%22 (= temp_22_0~3931@ temp_22_1~4004@))))) (=> (= temp_22_0~3931@ temp_22_1~4004@) (=> (= temp_23_0~4157@ (Mul (Mul (Add (Mul d23~192@ 5) (Mul d23~192@ c23~190@)) (Mul (Mul b23~188@ 82) (Mul a23~186@ a23~186@))) (Mul (Mul (Mul a23~186@ b23~188@) (Mul a23~186@ b23~188@)) (Mul (Mul c23~190@ c23~190@) (Sub d23~192@ d23~192@))))) (=> (= temp_23_1~4246@ (Mul (Mul (Add (Mul d23~192@ 5) (Mul c23~190@ d23~192@)) (Mul (Mul b23~188@ 82) (Mul a23~186@ a23~186@))) (Mul (Mul (Mul a23~186@ b23~188@) (Mul a23~186@ b23~188@)) (Mul (Mul c23~190@ c23~190@) (Sub d23~192@ d23~192@))))) (=> (ens%main!nl_basics.lemma_mul_is_commutative. d23~192@ c23~190@) (=> %%location_label%%23 (= temp_23_0~4157@ temp_23_1~4246@))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(assert %%query%%)
(check-sat)
