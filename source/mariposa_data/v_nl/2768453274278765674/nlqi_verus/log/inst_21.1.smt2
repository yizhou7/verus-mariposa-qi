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
(set-info :comment ";; mariposa_data/v_nl//2768453274278765674/nlqi_verus/src/main.rs:7:1: 36:40 (#0)")
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
(declare-const tmp%27@ Int)
(declare-const tmp%28@ Int)
(declare-const tmp%29@ Int)
(declare-const tmp%30@ Int)
(declare-const tmp%31@ Int)
(declare-const temp_0_0~281@ Int)
(declare-const temp_0_1~322@ Int)
(declare-const temp_1_0~447@ Int)
(declare-const temp_1_1~580@ Int)
(declare-const temp_2_0~751@ Int)
(declare-const temp_2_1~816@ Int)
(declare-const temp_3_0~929@ Int)
(declare-const temp_3_1~1006@ Int)
(declare-const temp_4_0~1103@ Int)
(declare-const temp_4_1~1164@ Int)
(declare-const temp_5_0~1281@ Int)
(declare-const temp_5_1~1370@ Int)
(declare-const temp_6_0~1423@ Int)
(declare-const temp_6_1~1448@ Int)
(declare-const temp_7_0~1521@ Int)
(declare-const temp_7_1~1558@ Int)
(declare-const temp_8_0~1655@ Int)
(declare-const temp_8_1~1716@ Int)
(declare-const temp_9_0~1851@ Int)
(declare-const temp_9_1~1940@ Int)
(declare-const temp_10_0~2049@ Int)
(declare-const temp_10_1~2110@ Int)
(declare-const temp_11_0~2175@ Int)
(declare-const temp_11_1~2212@ Int)
(declare-const temp_12_0~2323@ Int)
(declare-const temp_12_1~2400@ Int)
(declare-const temp_13_0~2497@ Int)
(declare-const temp_13_1~2558@ Int)
(declare-const temp_14_0~2653@ Int)
(declare-const temp_14_1~2714@ Int)
(declare-const temp_15_0~2813@ Int)
(declare-const temp_15_1~2878@ Int)
(declare-const temp_16_0~2985@ Int)
(declare-const temp_16_1~3058@ Int)
(declare-const temp_17_0~3191@ Int)
(declare-const temp_17_1~3276@ Int)
(declare-const temp_18_0~3417@ Int)
(declare-const temp_18_1~3454@ Int)
(declare-const temp_19_0~3583@ Int)
(declare-const temp_19_1~3660@ Int)
(declare-const temp_20_0~3801@ Int)
(declare-const temp_20_1~3878@ Int)
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
(declare-const %%query%% Bool)
(assert (=> %%query%% (not (=> (= temp_0_0~281@ (Mul (Add b0~4@ (Mul (Sub c0~6@ d0~8@) (Mul d0~8@ d0~8@))) (Mul b0~4@ (Mul (Mul b0~4@ c0~6@) (Sub b0~4@ b0~4@))))) (=> (= temp_0_1~322@ (Mul (Add b0~4@ (Mul (Mul d0~8@ d0~8@) (Sub c0~6@ d0~8@))) (Mul b0~4@ (Mul (Mul b0~4@ c0~6@) (Sub b0~4@ b0~4@))))) (and (=> (= tmp%1@ (Sub c0~6@ d0~8@)) (=> (= tmp%2@ (Mul d0~8@ d0~8@)) (=> (ens%main!nl_basics.lemma_mul_is_commutative. tmp%1@ tmp%2@) (=> %%location_label%%0 (= temp_0_0~281@ temp_0_1~322@))))) (=> (= temp_0_0~281@ temp_0_1~322@) (=> (= temp_1_0~447@ (Mul (Sub (Mul (Sub 85 c1~14@) (Mul b1~12@ c1~14@)) (Mul (Mul c1~14@ c1~14@) (Mul d1~16@ b1~12@))) (Add (Mul (Mul 29 c1~14@) (Mul c1~14@ d1~16@)) (Mul (Mul c1~14@ c1~14@) (Mul d1~16@ c1~14@))))) (=> (= temp_1_1~580@ (Add (Mul (Sub (Mul (Sub 85 c1~14@) (Mul b1~12@ c1~14@)) (Mul (Mul c1~14@ c1~14@) (Mul d1~16@ b1~12@))) (Mul (Mul 29 c1~14@) (Mul c1~14@ d1~16@))) (Mul (Sub (Mul (Sub 85 c1~14@) (Mul b1~12@ c1~14@)) (Mul (Mul c1~14@ c1~14@) (Mul d1~16@ b1~12@))) (Mul (Mul c1~14@ c1~14@) (Mul d1~16@ c1~14@))))) (and (=> (= tmp%3@ (Sub (Mul (Sub 85 c1~14@) (Mul b1~12@ c1~14@)) (Mul (Mul c1~14@ c1~14@) (Mul d1~16@ b1~12@)))) (=> (= tmp%4@ (Mul (Mul 29 c1~14@) (Mul c1~14@ d1~16@))) (=> (= tmp%5@ (Mul (Mul c1~14@ c1~14@) (Mul d1~16@ c1~14@))) (=> (ens%main!nl_basics.lemma_mul_is_distributive. tmp%3@ tmp%4@ tmp%5@) (=> %%location_label%%1 (= temp_1_0~447@ temp_1_1~580@)))))) (=> (= temp_1_0~447@ temp_1_1~580@) (=> (= temp_2_0~751@ (Add (Mul (Add (Mul b2~20@ c2~22@) (Mul b2~20@ d2~24@)) (Mul (Add a2~18@ b2~20@) (Mul c2~22@ c2~22@))) (Mul (Mul (Mul a2~18@ b2~20@) (Add b2~20@ c2~22@)) (Mul (Mul c2~22@ b2~20@) (Mul b2~20@ b2~20@))))) (=> (= temp_2_1~816@ (Add (Mul (Add (Mul b2~20@ c2~22@) (Mul b2~20@ d2~24@)) (Mul (Add a2~18@ b2~20@) (Mul c2~22@ c2~22@))) (Mul (Mul (Mul a2~18@ b2~20@) (Add b2~20@ c2~22@)) (Mul (Mul b2~20@ b2~20@) (Mul c2~22@ b2~20@))))) (and (=> (= tmp%6@ (Mul c2~22@ b2~20@)) (=> (= tmp%7@ (Mul b2~20@ b2~20@)) (=> (ens%main!nl_basics.lemma_mul_is_commutative. tmp%6@ tmp%7@) (=> %%location_label%%2 (= temp_2_0~751@ temp_2_1~816@))))) (=> (= temp_2_0~751@ temp_2_1~816@) (=> (= temp_3_0~929@ (Mul (Mul (Sub (Add a3~26@ b3~28@) (Mul 85 a3~26@)) (Mul (Add d3~32@ d3~32@) (Mul c3~30@ c3~30@))) (Mul (Mul (Mul c3~30@ c3~30@) (Mul c3~30@ c3~30@)) (Mul (Mul d3~32@ c3~30@) (Mul b3~28@ d3~32@))))) (=> (= temp_3_1~1006@ (Mul (Mul (Sub (Add a3~26@ b3~28@) (Mul 85 a3~26@)) (Mul (Mul c3~30@ c3~30@) (Add d3~32@ d3~32@))) (Mul (Mul (Mul c3~30@ c3~30@) (Mul c3~30@ c3~30@)) (Mul (Mul d3~32@ c3~30@) (Mul b3~28@ d3~32@))))) (and (=> (= tmp%8@ (Add d3~32@ d3~32@)) (=> (= tmp%9@ (Mul c3~30@ c3~30@)) (=> (ens%main!nl_basics.lemma_mul_is_commutative. tmp%8@ tmp%9@) (=> %%location_label%%3 (= temp_3_0~929@ temp_3_1~1006@))))) (=> (= temp_3_0~929@ temp_3_1~1006@) (=> (= temp_4_0~1103@ (Mul (Mul (Mul (Mul a4~34@ b4~36@) b4~36@) (Mul (Sub d4~40@ d4~40@) (Sub c4~38@ c4~38@))) (Add (Mul (Mul a4~34@ b4~36@) (Sub c4~38@ c4~38@)) (Mul (Mul b4~36@ b4~36@) (Add d4~40@ a4~34@))))) (=> (= temp_4_1~1164@ (Mul (Mul (Mul (Mul a4~34@ b4~36@) b4~36@) (Mul (Sub d4~40@ d4~40@) (Sub c4~38@ c4~38@))) (Add (Mul (Mul b4~36@ a4~34@) (Sub c4~38@ c4~38@)) (Mul (Mul b4~36@ b4~36@) (Add d4~40@ a4~34@))))) (and (=> (ens%main!nl_basics.lemma_mul_is_commutative. a4~34@ b4~36@) (=> %%location_label%%4 (= temp_4_0~1103@ temp_4_1~1164@))) (=> (= temp_4_0~1103@ temp_4_1~1164@) (=> (= temp_5_0~1281@ (Sub (Sub (Mul (Mul b5~44@ a5~42@) (Mul c5~46@ a5~42@)) (Mul (Add 98 c5~46@) (Mul d5~48@ b5~44@))) (Mul (Mul (Mul c5~46@ a5~42@) (Mul a5~42@ c5~46@)) (Mul (Mul d5~48@ b5~44@) (Mul c5~46@ 54))))) (=> (= temp_5_1~1370@ (Sub (Sub (Mul (Mul b5~44@ a5~42@) (Mul a5~42@ c5~46@)) (Mul (Add 98 c5~46@) (Mul d5~48@ b5~44@))) (Mul (Mul (Mul c5~46@ a5~42@) (Mul a5~42@ c5~46@)) (Mul (Mul d5~48@ b5~44@) (Mul c5~46@ 54))))) (and (=> (ens%main!nl_basics.lemma_mul_is_commutative. c5~46@ a5~42@) (=> %%location_label%%5 (= temp_5_0~1281@ temp_5_1~1370@))) (=> (= temp_5_0~1281@ temp_5_1~1370@) (=> (= temp_6_0~1423@ (Mul (Mul d6~56@ c6~54@) (Mul (Mul (Mul c6~54@ c6~54@) c6~54@) c6~54@))) (=> (= temp_6_1~1448@ (Mul (Mul d6~56@ c6~54@) (Mul c6~54@ (Mul (Mul c6~54@ c6~54@) c6~54@)))) (and (=> (= tmp%10@ (Mul (Mul c6~54@ c6~54@) c6~54@)) (=> (ens%main!nl_basics.lemma_mul_is_commutative. tmp%10@ c6~54@) (=> %%location_label%%6 (= temp_6_0~1423@ temp_6_1~1448@)))) (=> (= temp_6_0~1423@ temp_6_1~1448@) (=> (= temp_7_0~1521@ (Mul a7~58@ (Mul (Mul (Mul c7~62@ b7~60@) (Mul a7~58@ c7~62@)) (Mul (Mul b7~60@ c7~62@) (Add b7~60@ a7~58@))))) (=> (= temp_7_1~1558@ (Mul a7~58@ (Mul (Mul (Mul a7~58@ c7~62@) (Mul c7~62@ b7~60@)) (Mul (Mul b7~60@ c7~62@) (Add b7~60@ a7~58@))))) (and (=> (= tmp%11@ (Mul c7~62@ b7~60@)) (=> (= tmp%12@ (Mul a7~58@ c7~62@)) (=> (ens%main!nl_basics.lemma_mul_is_commutative. tmp%11@ tmp%12@) (=> %%location_label%%7 (= temp_7_0~1521@ temp_7_1~1558@))))) (=> (= temp_7_0~1521@ temp_7_1~1558@) (=> (= temp_8_0~1655@ (Mul (Mul (Mul (Sub b8~68@ c8~70@) (Mul a8~66@ b8~68@)) (Mul (Add c8~70@ d8~72@) a8~66@)) (Mul (Add (Mul a8~66@ b8~68@) (Mul c8~70@ b8~68@)) (Mul (Add d8~72@ a8~66@) (Mul a8~66@ d8~72@))))) (=> (= temp_8_1~1716@ (Mul (Mul (Sub b8~68@ c8~70@) (Mul (Mul a8~66@ b8~68@) (Mul (Add c8~70@ d8~72@) a8~66@))) (Mul (Add (Mul a8~66@ b8~68@) (Mul c8~70@ b8~68@)) (Mul (Add d8~72@ a8~66@) (Mul a8~66@ d8~72@))))) (and (=> (= tmp%13@ (Sub b8~68@ c8~70@)) (=> (= tmp%14@ (Mul a8~66@ b8~68@)) (=> (= tmp%15@ (Mul (Add c8~70@ d8~72@) a8~66@)) (=> (ens%main!nl_basics.lemma_mul_is_associative. tmp%13@ tmp%14@ tmp%15@) (=> %%location_label%%8 (= temp_8_0~1655@ temp_8_1~1716@)))))) (=> (= temp_8_0~1655@ temp_8_1~1716@) (=> (= temp_9_0~1851@ (Mul (Mul (Mul (Mul d9~80@ a9~74@) (Mul 52 d9~80@)) (Mul (Mul c9~78@ c9~78@) (Mul d9~80@ b9~76@))) (Mul (Sub (Mul a9~74@ a9~74@) (Mul c9~78@ c9~78@)) (Mul (Mul d9~80@ a9~74@) (Mul 20 a9~74@))))) (=> (= temp_9_1~1940@ (Mul (Mul (Mul (Mul 52 d9~80@) (Mul d9~80@ a9~74@)) (Mul (Mul c9~78@ c9~78@) (Mul d9~80@ b9~76@))) (Mul (Sub (Mul a9~74@ a9~74@) (Mul c9~78@ c9~78@)) (Mul (Mul d9~80@ a9~74@) (Mul 20 a9~74@))))) (and (=> (= tmp%16@ (Mul d9~80@ a9~74@)) (=> (= tmp%17@ (Mul 52 d9~80@)) (=> (ens%main!nl_basics.lemma_mul_is_commutative. tmp%16@ tmp%17@) (=> %%location_label%%9 (= temp_9_0~1851@ temp_9_1~1940@))))) (=> (= temp_9_0~1851@ temp_9_1~1940@) (=> (= temp_10_0~2049@ (Mul (Mul (Mul a10~82@ (Add b10~84@ b10~84@)) (Mul (Sub b10~84@ b10~84@) (Mul a10~82@ c10~86@))) (Sub (Mul (Sub c10~86@ d10~88@) (Mul a10~82@ c10~86@)) (Mul (Add c10~86@ a10~82@) (Mul b10~84@ d10~88@))))) (=> (= temp_10_1~2110@ (Mul (Mul (Mul a10~82@ (Add b10~84@ b10~84@)) (Mul (Sub b10~84@ b10~84@) (Mul a10~82@ c10~86@))) (Sub (Mul (Sub c10~86@ d10~88@) (Mul a10~82@ c10~86@)) (Mul (Add c10~86@ a10~82@) (Mul d10~88@ b10~84@))))) (and (=> (ens%main!nl_basics.lemma_mul_is_commutative. b10~84@ d10~88@) (=> %%location_label%%10 (= temp_10_0~2049@ temp_10_1~2110@))) (=> (= temp_10_0~2049@ temp_10_1~2110@) (=> (= temp_11_0~2175@ (Mul (Mul (Mul (Mul d11~96@ a11~90@) (Mul b11~92@ c11~94@)) (Mul (Mul a11~90@ a11~90@) (Sub b11~92@ b11~92@))) d11~96@)) (=> (= temp_11_1~2212@ (Mul (Mul (Mul (Mul d11~96@ a11~90@) (Mul b11~92@ c11~94@)) (Mul a11~90@ (Mul a11~90@ (Sub b11~92@ b11~92@)))) d11~96@)) (and (=> (= tmp%18@ (Sub b11~92@ b11~92@)) (=> (ens%main!nl_basics.lemma_mul_is_associative. a11~90@ a11~90@ tmp%18@) (=> %%location_label%%11 (= temp_11_0~2175@ temp_11_1~2212@)))) (=> (= temp_11_0~2175@ temp_11_1~2212@) (=> (= temp_12_0~2323@ (Mul (Mul (Add (Mul b12~100@ c12~102@) (Mul d12~104@ a12~98@)) (Sub (Mul 15 c12~102@) (Mul d12~104@ c12~102@))) (Mul (Mul (Mul b12~100@ a12~98@) (Add b12~100@ b12~100@)) (Mul (Mul b12~100@ a12~98@) (Mul a12~98@ b12~100@))))) (=> (= temp_12_1~2400@ (Mul (Mul (Add (Mul b12~100@ c12~102@) (Mul d12~104@ a12~98@)) (Sub (Mul 15 c12~102@) (Mul d12~104@ c12~102@))) (Mul (Mul (Mul b12~100@ a12~98@) (Add b12~100@ b12~100@)) (Mul (Mul a12~98@ b12~100@) (Mul b12~100@ a12~98@))))) (and (=> (= tmp%19@ (Mul b12~100@ a12~98@)) (=> (= tmp%20@ (Mul a12~98@ b12~100@)) (=> (ens%main!nl_basics.lemma_mul_is_commutative. tmp%19@ tmp%20@) (=> %%location_label%%12 (= temp_12_0~2323@ temp_12_1~2400@))))) (=> (= temp_12_0~2323@ temp_12_1~2400@) (=> (= temp_13_0~2497@ (Sub (Mul (Mul (Mul a13~106@ a13~106@) (Mul b13~108@ c13~110@)) (Mul (Mul d13~112@ d13~112@) (Mul c13~110@ d13~112@))) (Mul (Mul b13~108@ (Mul a13~106@ b13~108@)) (Mul (Mul b13~108@ a13~106@) (Mul d13~112@ c13~110@))))) (=> (= temp_13_1~2558@ (Sub (Mul (Mul (Mul (Mul a13~106@ a13~106@) b13~108@) c13~110@) (Mul (Mul d13~112@ d13~112@) (Mul c13~110@ d13~112@))) (Mul (Mul b13~108@ (Mul a13~106@ b13~108@)) (Mul (Mul b13~108@ a13~106@) (Mul d13~112@ c13~110@))))) (and (=> (= tmp%21@ (Mul a13~106@ a13~106@)) (=> (ens%main!nl_basics.lemma_mul_is_associative. tmp%21@ b13~108@ c13~110@) (=> %%location_label%%13 (= temp_13_0~2497@ temp_13_1~2558@)))) (=> (= temp_13_0~2497@ temp_13_1~2558@) (=> (= temp_14_0~2653@ (Mul (Sub (Mul (Mul d14~120@ c14~118@) c14~118@) (Add (Mul c14~118@ c14~118@) (Add c14~118@ c14~118@))) (Mul (Mul (Mul b14~116@ d14~120@) (Mul a14~114@ c14~118@)) (Mul (Mul c14~118@ d14~120@) (Mul b14~116@ c14~118@))))) (=> (= temp_14_1~2714@ (Mul (Sub (Mul (Mul d14~120@ c14~118@) c14~118@) (Add (Mul c14~118@ c14~118@) (Add c14~118@ c14~118@))) (Mul (Mul (Mul b14~116@ d14~120@) (Mul a14~114@ c14~118@)) (Mul (Mul (Mul c14~118@ d14~120@) b14~116@) c14~118@)))) (and (=> (= tmp%22@ (Mul c14~118@ d14~120@)) (=> (ens%main!nl_basics.lemma_mul_is_associative. tmp%22@ b14~116@ c14~118@) (=> %%location_label%%14 (= temp_14_0~2653@ temp_14_1~2714@)))) (=> (= temp_14_0~2653@ temp_14_1~2714@) (=> (= temp_15_0~2813@ (Sub (Mul (Mul (Mul b15~124@ b15~124@) (Mul d15~128@ b15~124@)) (Mul (Add a15~122@ c15~126@) (Mul b15~124@ a15~122@))) (Mul (Mul (Mul c15~126@ d15~128@) (Mul d15~128@ a15~122@)) (Sub (Mul a15~122@ c15~126@) (Mul c15~126@ c15~126@))))) (=> (= temp_15_1~2878@ (Sub (Mul (Mul (Mul b15~124@ b15~124@) (Mul d15~128@ b15~124@)) (Mul (Add a15~122@ c15~126@) (Mul b15~124@ a15~122@))) (Mul (Mul (Mul (Mul c15~126@ d15~128@) d15~128@) a15~122@) (Sub (Mul a15~122@ c15~126@) (Mul c15~126@ c15~126@))))) (and (=> (= tmp%23@ (Mul c15~126@ d15~128@)) (=> (ens%main!nl_basics.lemma_mul_is_associative. tmp%23@ d15~128@ a15~122@) (=> %%location_label%%15 (= temp_15_0~2813@ temp_15_1~2878@)))) (=> (= temp_15_0~2813@ temp_15_1~2878@) (=> (= temp_16_0~2985@ (Mul (Mul (Mul (Mul a16~130@ b16~132@) (Mul c16~134@ b16~132@)) (Sub (Mul 0 d16~136@) (Mul b16~132@ a16~130@))) (Mul (Mul (Mul c16~134@ a16~130@) (Add a16~130@ a16~130@)) (Mul c16~134@ (Mul a16~130@ d16~136@))))) (=> (= temp_16_1~3058@ (Mul (Mul (Mul (Mul a16~130@ b16~132@) (Mul c16~134@ b16~132@)) (Sub (Mul 0 d16~136@) (Mul b16~132@ a16~130@))) (Mul (Mul c16~134@ (Mul a16~130@ d16~136@)) (Mul (Mul c16~134@ a16~130@) (Add a16~130@ a16~130@))))) (and (=> (= tmp%24@ (Mul (Mul c16~134@ a16~130@) (Add a16~130@ a16~130@))) (=> (= tmp%25@ (Mul c16~134@ (Mul a16~130@ d16~136@))) (=> (ens%main!nl_basics.lemma_mul_is_commutative. tmp%24@ tmp%25@) (=> %%location_label%%16 (= temp_16_0~2985@ temp_16_1~3058@))))) (=> (= temp_16_0~2985@ temp_16_1~3058@) (=> (= temp_17_0~3191@ (Mul (Add (Mul (Mul 46 b17~140@) (Mul d17~144@ c17~142@)) (Mul b17~140@ (Add d17~144@ a17~138@))) (Mul (Mul (Sub d17~144@ b17~140@) (Mul d17~144@ d17~144@)) (Mul (Mul 67 a17~138@) (Mul b17~140@ d17~144@))))) (=> (= temp_17_1~3276@ (Mul (Mul (Mul (Sub d17~144@ b17~140@) (Mul d17~144@ d17~144@)) (Mul (Mul 67 a17~138@) (Mul b17~140@ d17~144@))) (Add (Mul (Mul 46 b17~140@) (Mul d17~144@ c17~142@)) (Mul b17~140@ (Add d17~144@ a17~138@))))) (and (=> (= tmp%26@ (Add (Mul (Mul 46 b17~140@) (Mul d17~144@ c17~142@)) (Mul b17~140@ (Add d17~144@ a17~138@)))) (=> (= tmp%27@ (Mul (Mul (Sub d17~144@ b17~140@) (Mul d17~144@ d17~144@)) (Mul (Mul 67 a17~138@) (Mul b17~140@ d17~144@)))) (=> (ens%main!nl_basics.lemma_mul_is_commutative. tmp%26@ tmp%27@) (=> %%location_label%%17 (= temp_17_0~3191@ temp_17_1~3276@))))) (=> (= temp_17_0~3191@ temp_17_1~3276@) (=> (= temp_18_0~3417@ (Sub (Mul (Add (Add d18~152@ c18~150@) (Sub d18~152@ d18~152@)) (Sub (Mul b18~148@ b18~148@) (Mul c18~150@ b18~148@))) c18~150@)) (=> (= temp_18_1~3454@ (Sub (Mul (Sub (Mul b18~148@ b18~148@) (Mul c18~150@ b18~148@)) (Add (Add d18~152@ c18~150@) (Sub d18~152@ d18~152@))) c18~150@)) (and (=> (= tmp%28@ (Add (Add d18~152@ c18~150@) (Sub d18~152@ d18~152@))) (=> (= tmp%29@ (Sub (Mul b18~148@ b18~148@) (Mul c18~150@ b18~148@))) (=> (ens%main!nl_basics.lemma_mul_is_commutative. tmp%28@ tmp%29@) (=> %%location_label%%18 (= temp_18_0~3417@ temp_18_1~3454@))))) (=> (= temp_18_0~3417@ temp_18_1~3454@) (=> (= temp_19_0~3583@ (Mul (Mul (Add (Mul d19~160@ 48) (Add d19~160@ d19~160@)) (Sub (Mul b19~156@ c19~158@) (Sub b19~156@ d19~160@))) (Mul d19~160@ (Mul (Mul 50 c19~158@) (Add b19~156@ a19~154@))))) (=> (= temp_19_1~3660@ (Mul (Mul (Sub (Mul b19~156@ c19~158@) (Sub b19~156@ d19~160@)) (Add (Mul d19~160@ 48) (Add d19~160@ d19~160@))) (Mul d19~160@ (Mul (Mul 50 c19~158@) (Add b19~156@ a19~154@))))) (and (=> (= tmp%30@ (Add (Mul d19~160@ 48) (Add d19~160@ d19~160@))) (=> (= tmp%31@ (Sub (Mul b19~156@ c19~158@) (Sub b19~156@ d19~160@))) (=> (ens%main!nl_basics.lemma_mul_is_commutative. tmp%30@ tmp%31@) (=> %%location_label%%19 (= temp_19_0~3583@ temp_19_1~3660@))))) (=> (= temp_19_0~3583@ temp_19_1~3660@) (=> (= temp_20_0~3801@ (Mul (Mul (Mul (Mul c20~166@ d20~168@) (Mul b20~164@ d20~168@)) (Mul (Sub a20~162@ c20~166@) (Mul d20~168@ c20~166@))) (Sub (Mul (Mul b20~164@ c20~166@) (Mul b20~164@ c20~166@)) (Mul (Mul 22 a20~162@) (Mul b20~164@ b20~164@))))) (=> (= temp_20_1~3878@ (Mul (Mul (Mul (Mul c20~166@ d20~168@) (Mul b20~164@ d20~168@)) (Mul (Sub a20~162@ c20~166@) (Mul d20~168@ c20~166@))) (Sub (Mul (Mul b20~164@ c20~166@) (Mul c20~166@ b20~164@)) (Mul (Mul 22 a20~162@) (Mul b20~164@ b20~164@))))) (=> (ens%main!nl_basics.lemma_mul_is_commutative. b20~164@ c20~166@) (=> %%location_label%%20 (= temp_20_0~3801@ temp_20_1~3878@))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(assert %%query%%)
(check-sat)
