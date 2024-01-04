(set-option :auto_config false)
(set-option :smt.mbqi false)
(set-option :smt.case_split 3)
(set-option :smt.qi.eager_threshold 100.0)
(set-option :smt.delay_units true)
(set-option :smt.arith.solver 2)
(set-option :smt.arith.nl false)
(set-option :timeout 5000)

;; Prelude

;; AIR prelude
(declare-sort %%Function%% 0)

(declare-sort FuelId 0)
(declare-sort Fuel 0)
(declare-const zero Fuel)
(declare-fun succ (Fuel) Fuel)
(declare-fun fuel_bool (FuelId) Bool)
(declare-fun fuel_bool_default (FuelId) Bool)
(declare-const fuel_defaults Bool)
(assert
 (=>
  fuel_defaults
  (forall ((id FuelId)) (!
    (= (fuel_bool id) (fuel_bool_default id))
    :pattern ((fuel_bool id))
    :qid prelude_fuel_defaults
    :skolemid skolem_prelude_fuel_defaults
))))
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
(assert
 (forall ((i Int)) (!
   (= i (const_int (CONST_INT i)))
   :pattern ((CONST_INT i))
   :qid prelude_type_id_const_int
   :skolemid skolem_prelude_type_id_const_int
)))
(assert
 (forall ((b Bool)) (!
   (has_type (B b) BOOL)
   :pattern ((has_type (B b) BOOL))
   :qid prelude_has_type_bool
   :skolemid skolem_prelude_has_type_bool
)))
(assert
 (forall ((x Poly) (t Type)) (!
   (and
    (has_type (as_type x t) t)
    (=>
     (has_type x t)
     (= x (as_type x t))
   ))
   :pattern ((as_type x t))
   :qid prelude_as_type
   :skolemid skolem_prelude_as_type
)))
(assert
 (forall ((x %%Function%%)) (!
   (= (mk_fun x) x)
   :pattern ((mk_fun x))
   :qid prelude_mk_fun
   :skolemid skolem_prelude_mk_fun
)))
(assert
 (forall ((x Bool)) (!
   (= x (%B (B x)))
   :pattern ((B x))
   :qid prelude_unbox_box_bool
   :skolemid skolem_prelude_unbox_box_bool
)))
(assert
 (forall ((x Int)) (!
   (= x (%I (I x)))
   :pattern ((I x))
   :qid prelude_unbox_box_int
   :skolemid skolem_prelude_unbox_box_int
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x BOOL)
    (= x (B (%B x)))
   )
   :pattern ((has_type x BOOL))
   :qid prelude_box_unbox_bool
   :skolemid skolem_prelude_box_unbox_bool
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x INT)
    (= x (I (%I x)))
   )
   :pattern ((has_type x INT))
   :qid prelude_box_unbox_int
   :skolemid skolem_prelude_box_unbox_int
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x NAT)
    (= x (I (%I x)))
   )
   :pattern ((has_type x NAT))
   :qid prelude_box_unbox_nat
   :skolemid skolem_prelude_box_unbox_nat
)))
(assert
 (forall ((bits Int) (x Poly)) (!
   (=>
    (has_type x (UINT bits))
    (= x (I (%I x)))
   )
   :pattern ((has_type x (UINT bits)))
   :qid prelude_box_unbox_uint
   :skolemid skolem_prelude_box_unbox_uint
)))
(assert
 (forall ((bits Int) (x Poly)) (!
   (=>
    (has_type x (SINT bits))
    (= x (I (%I x)))
   )
   :pattern ((has_type x (SINT bits)))
   :qid prelude_box_unbox_sint
   :skolemid skolem_prelude_box_unbox_sint
)))
(assert
 (forall ((x Int)) (!
   (= (str%from_strlit (str%new_strlit x)) x)
   :pattern ((str%new_strlit x))
   :qid prelude_strlit_injective
   :skolemid skolem_prelude_strlit_injective
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x STRSLICE)
    (= x (S (%S x)))
   )
   :pattern ((has_type x STRSLICE))
   :qid prelude_box_unbox_strslice
   :skolemid skolem_prelude_box_unbox_strslice
)))
(assert
 (forall ((x StrSlice)) (!
   (= x (%S (S x)))
   :pattern ((S x))
   :qid prelude_unbox_box_strslice
   :skolemid skolem_prelude_unbox_box_strslice
)))
(assert
 (forall ((x StrSlice)) (!
   (has_type (S x) STRSLICE)
   :pattern ((has_type (S x) STRSLICE))
   :qid prelude_has_type_strslice
   :skolemid skolem_prelude_has_type_strslice
)))
(declare-fun ext_eq (Bool Type Poly Poly) Bool)
(assert
 (forall ((deep Bool) (t Type) (x Poly) (y Poly)) (!
   (= (= x y) (ext_eq deep t x y))
   :pattern ((ext_eq deep t x y))
   :qid prelude_ext_eq
   :skolemid skolem_prelude_ext_eq
)))
(declare-const SZ Int)
(assert
 (or
  (= SZ 32)
  (= SZ 64)
))
(declare-fun uHi (Int) Int)
(declare-fun iLo (Int) Int)
(declare-fun iHi (Int) Int)
(assert
 (= (uHi 8) 256)
)
(assert
 (= (uHi 16) 65536)
)
(assert
 (= (uHi 32) 4294967296)
)
(assert
 (= (uHi 64) 18446744073709551616)
)
(assert
 (= (uHi 128) (+ 1 340282366920938463463374607431768211455))
)
(assert
 (= (iLo 8) (- 128))
)
(assert
 (= (iLo 16) (- 32768))
)
(assert
 (= (iLo 32) (- 2147483648))
)
(assert
 (= (iLo 64) (- 9223372036854775808))
)
(assert
 (= (iLo 128) (- 170141183460469231731687303715884105728))
)
(assert
 (= (iHi 8) 128)
)
(assert
 (= (iHi 16) 32768)
)
(assert
 (= (iHi 32) 2147483648)
)
(assert
 (= (iHi 64) 9223372036854775808)
)
(assert
 (= (iHi 128) 170141183460469231731687303715884105728)
)
(declare-fun nClip (Int) Int)
(declare-fun uClip (Int Int) Int)
(declare-fun iClip (Int Int) Int)
(assert
 (forall ((i Int)) (!
   (and
    (<= 0 (nClip i))
    (=>
     (<= 0 i)
     (= i (nClip i))
   ))
   :pattern ((nClip i))
   :qid prelude_nat_clip
   :skolemid skolem_prelude_nat_clip
)))
(assert
 (forall ((bits Int) (i Int)) (!
   (and
    (<= 0 (uClip bits i))
    (< (uClip bits i) (uHi bits))
    (=>
     (and
      (<= 0 i)
      (< i (uHi bits))
     )
     (= i (uClip bits i))
   ))
   :pattern ((uClip bits i))
   :qid prelude_u_clip
   :skolemid skolem_prelude_u_clip
)))
(assert
 (forall ((bits Int) (i Int)) (!
   (and
    (<= (iLo bits) (iClip bits i))
    (< (iClip bits i) (iHi bits))
    (=>
     (and
      (<= (iLo bits) i)
      (< i (iHi bits))
     )
     (= i (iClip bits i))
   ))
   :pattern ((iClip bits i))
   :qid prelude_i_clip
   :skolemid skolem_prelude_i_clip
)))
(declare-fun uInv (Int Int) Bool)
(declare-fun iInv (Int Int) Bool)
(assert
 (forall ((bits Int) (i Int)) (!
   (= (uInv bits i) (and
     (<= 0 i)
     (< i (uHi bits))
   ))
   :pattern ((uInv bits i))
   :qid prelude_u_inv
   :skolemid skolem_prelude_u_inv
)))
(assert
 (forall ((bits Int) (i Int)) (!
   (= (iInv bits i) (and
     (<= (iLo bits) i)
     (< i (iHi bits))
   ))
   :pattern ((iInv bits i))
   :qid prelude_i_inv
   :skolemid skolem_prelude_i_inv
)))
(assert
 (forall ((x Int)) (!
   (has_type (I x) INT)
   :pattern ((has_type (I x) INT))
   :qid prelude_has_type_int
   :skolemid skolem_prelude_has_type_int
)))
(assert
 (forall ((x Int)) (!
   (=>
    (<= 0 x)
    (has_type (I x) NAT)
   )
   :pattern ((has_type (I x) NAT))
   :qid prelude_has_type_nat
   :skolemid skolem_prelude_has_type_nat
)))
(assert
 (forall ((bits Int) (x Int)) (!
   (=>
    (uInv bits x)
    (has_type (I x) (UINT bits))
   )
   :pattern ((has_type (I x) (UINT bits)))
   :qid prelude_has_type_uint
   :skolemid skolem_prelude_has_type_uint
)))
(assert
 (forall ((bits Int) (x Int)) (!
   (=>
    (iInv bits x)
    (has_type (I x) (SINT bits))
   )
   :pattern ((has_type (I x) (SINT bits)))
   :qid prelude_has_type_sint
   :skolemid skolem_prelude_has_type_sint
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x NAT)
    (<= 0 (%I x))
   )
   :pattern ((has_type x NAT))
   :qid prelude_unbox_int
   :skolemid skolem_prelude_unbox_int
)))
(assert
 (forall ((bits Int) (x Poly)) (!
   (=>
    (has_type x (UINT bits))
    (uInv bits (%I x))
   )
   :pattern ((has_type x (UINT bits)))
   :qid prelude_unbox_uint
   :skolemid skolem_prelude_unbox_uint
)))
(assert
 (forall ((bits Int) (x Poly)) (!
   (=>
    (has_type x (SINT bits))
    (iInv bits (%I x))
   )
   :pattern ((has_type x (SINT bits)))
   :qid prelude_unbox_sint
   :skolemid skolem_prelude_unbox_sint
)))
(declare-fun Add (Int Int) Int)
(declare-fun Sub (Int Int) Int)
(declare-fun Mul (Int Int) Int)
(declare-fun EucDiv (Int Int) Int)
(declare-fun EucMod (Int Int) Int)
(assert
 (forall ((x Int) (y Int)) (!
   (= (Add x y) (+ x y))
   :pattern ((Add x y))
   :qid prelude_add
   :skolemid skolem_prelude_add
)))
(assert
 (forall ((x Int) (y Int)) (!
   (= (Sub x y) (- x y))
   :pattern ((Sub x y))
   :qid prelude_sub
   :skolemid skolem_prelude_sub
)))
(assert
 (forall ((x Int) (y Int)) (!
   (= (Mul x y) (* x y))
   :pattern ((Mul x y))
   :qid prelude_mul
   :skolemid skolem_prelude_mul
)))
(assert
 (forall ((x Int) (y Int)) (!
   (= (EucDiv x y) (div x y))
   :pattern ((EucDiv x y))
   :qid prelude_eucdiv
   :skolemid skolem_prelude_eucdiv
)))
(assert
 (forall ((x Int) (y Int)) (!
   (= (EucMod x y) (mod x y))
   :pattern ((EucMod x y))
   :qid prelude_eucmod
   :skolemid skolem_prelude_eucmod
)))
(assert
 (forall ((x Int) (y Int)) (!
   (=>
    (and
     (<= 0 x)
     (<= 0 y)
    )
    (<= 0 (Mul x y))
   )
   :pattern ((Mul x y))
   :qid prelude_mul_nats
   :skolemid skolem_prelude_mul_nats
)))
(assert
 (forall ((x Int) (y Int)) (!
   (=>
    (and
     (<= 0 x)
     (< 0 y)
    )
    (and
     (<= 0 (EucDiv x y))
     (<= (EucDiv x y) x)
   ))
   :pattern ((EucDiv x y))
   :qid prelude_div_unsigned_in_bounds
   :skolemid skolem_prelude_div_unsigned_in_bounds
)))
(assert
 (forall ((x Int) (y Int)) (!
   (=>
    (and
     (<= 0 x)
     (< 0 y)
    )
    (and
     (<= 0 (EucMod x y))
     (< (EucMod x y) y)
   ))
   :pattern ((EucMod x y))
   :qid prelude_mod_unsigned_in_bounds
   :skolemid skolem_prelude_mod_unsigned_in_bounds
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x CHAR)
    (= x (C (%C x)))
   )
   :pattern ((has_type x CHAR))
   :qid prelude_box_unbox_char
   :skolemid skolem_prelude_box_unbox_char
)))
(assert
 (forall ((x Char)) (!
   (= x (%C (C x)))
   :pattern ((C x))
   :qid prelude_unbox_box_char
   :skolemid skolem_prelude_unbox_box_char
)))
(assert
 (forall ((x Char)) (!
   (has_type (C x) CHAR)
   :pattern ((has_type (C x) CHAR))
   :qid prelude_has_type_char
   :skolemid skolem_prelude_has_type_char
)))
(assert
 (forall ((x Int)) (!
   (=>
    (and
     (<= 0 x)
     (< x (uHi 32))
    )
    (= x (char%to_unicode (char%from_unicode x)))
   )
   :pattern ((char%from_unicode x))
   :qid prelude_char_injective
   :skolemid skolem_prelude_char_injective
)))
(assert
 (forall ((c Char)) (!
   (and
    (<= 0 (char%to_unicode c))
    (< (char%to_unicode c) (uHi 32))
   )
   :pattern ((char%to_unicode c))
   :qid prelude_to_unicode_bounds
   :skolemid skolem_prelude_to_unicode_bounds
)))
(declare-fun height (Poly) Height)
(declare-fun height_lt (Height Height) Bool)
(assert
 (forall ((x Height) (y Height)) (!
   (= (height_lt x y) (and
     ((_ partial-order 0) x y)
     (not (= x y))
   ))
   :pattern ((height_lt x y))
   :qid prelude_height_lt
   :skolemid skolem_prelude_height_lt
)))
(declare-fun fun_from_recursive_field (Poly) Poly)
(declare-fun check_decrease_int (Int Int Bool) Bool)
(assert
 (forall ((cur Int) (prev Int) (otherwise Bool)) (!
   (= (check_decrease_int cur prev otherwise) (or
     (and
      (<= 0 cur)
      (< cur prev)
     )
     (and
      (= cur prev)
      otherwise
   )))
   :pattern ((check_decrease_int cur prev otherwise))
   :qid prelude_check_decrease_int
   :skolemid skolem_prelude_check_decrease_int
)))
(declare-fun check_decrease_height (Poly Poly Bool) Bool)
(assert
 (forall ((cur Poly) (prev Poly) (otherwise Bool)) (!
   (= (check_decrease_height cur prev otherwise) (or
     (height_lt (height cur) (height prev))
     (and
      (= (height cur) (height prev))
      otherwise
   )))
   :pattern ((check_decrease_height cur prev otherwise))
   :qid prelude_check_decrease_height
   :skolemid skolem_prelude_check_decrease_height
)))
(declare-fun uintxor (Int Poly Poly) Int)
(declare-fun uintand (Int Poly Poly) Int)
(declare-fun uintor (Int Poly Poly) Int)
(declare-fun uintshr (Int Poly Poly) Int)
(declare-fun uintshl (Int Poly Poly) Int)
(declare-fun uintnot (Int Poly) Int)
(declare-fun singular_mod (Int Int) Int)
(assert
 (forall ((x Int) (y Int)) (!
   (=>
    (not (= y 0))
    (= (EucMod x y) (singular_mod x y))
   )
   :pattern ((singular_mod x y))
   :qid prelude_singularmod
   :skolemid skolem_prelude_singularmod
)))
(declare-fun closure_req (Type Dcr Type Poly Poly) Bool)
(declare-fun closure_ens (Type Dcr Type Poly Poly Poly) Bool)

;; MODULE 'root module'

;; Fuel
(assert
 true
)

;; Datatypes
(declare-datatypes ((tuple%0. 0)) (((tuple%0./tuple%0))))
(declare-const TYPE%tuple%0. Type)
(declare-fun Poly%tuple%0. (tuple%0.) Poly)
(declare-fun %Poly%tuple%0. (Poly) tuple%0.)
(assert
 (forall ((x@ tuple%0.)) (!
   (= x@ (%Poly%tuple%0. (Poly%tuple%0. x@)))
   :pattern ((Poly%tuple%0. x@))
   :qid internal_crate__tuple__0_box_axiom_definition
   :skolemid skolem_internal_crate__tuple__0_box_axiom_definition
)))
(assert
 (forall ((x@ Poly)) (!
   (=>
    (has_type x@ TYPE%tuple%0.)
    (= x@ (Poly%tuple%0. (%Poly%tuple%0. x@)))
   )
   :pattern ((has_type x@ TYPE%tuple%0.))
   :qid internal_crate__tuple__0_unbox_axiom_definition
   :skolemid skolem_internal_crate__tuple__0_unbox_axiom_definition
)))
(assert
 (forall ((x@ tuple%0.)) (!
   (has_type (Poly%tuple%0. x@) TYPE%tuple%0.)
   :pattern ((has_type (Poly%tuple%0. x@) TYPE%tuple%0.))
   :qid internal_crate__tuple__0_has_type_always_definition
   :skolemid skolem_internal_crate__tuple__0_has_type_always_definition
)))

;; Function-Specs main::nl_basics::lemma_mul_is_associative
(declare-fun ens%main!nl_basics.lemma_mul_is_associative. (Int Int Int) Bool)
(assert
 (forall ((x~2@ Int) (y~4@ Int) (z~6@ Int)) (!
   (= (ens%main!nl_basics.lemma_mul_is_associative. x~2@ y~4@ z~6@) (= (Mul x~2@ (Mul y~4@
       z~6@
      )
     ) (Mul (Mul x~2@ y~4@) z~6@)
   ))
   :pattern ((ens%main!nl_basics.lemma_mul_is_associative. x~2@ y~4@ z~6@))
   :qid internal_ens__main!nl_basics.lemma_mul_is_associative._definition
   :skolemid skolem_internal_ens__main!nl_basics.lemma_mul_is_associative._definition
)))

;; Function-Specs main::nl_basics::lemma_mul_is_commutative
(declare-fun ens%main!nl_basics.lemma_mul_is_commutative. (Int Int) Bool)
(assert
 (forall ((x~2@ Int) (y~4@ Int)) (!
   (= (ens%main!nl_basics.lemma_mul_is_commutative. x~2@ y~4@) (= (Mul x~2@ y~4@) (Mul
      y~4@ x~2@
   )))
   :pattern ((ens%main!nl_basics.lemma_mul_is_commutative. x~2@ y~4@))
   :qid internal_ens__main!nl_basics.lemma_mul_is_commutative._definition
   :skolemid skolem_internal_ens__main!nl_basics.lemma_mul_is_commutative._definition
)))

;; Function-Specs main::nl_basics::lemma_mul_is_distributive
(declare-fun ens%main!nl_basics.lemma_mul_is_distributive. (Int Int Int) Bool)
(assert
 (forall ((x~2@ Int) (y~4@ Int) (z~6@ Int)) (!
   (= (ens%main!nl_basics.lemma_mul_is_distributive. x~2@ y~4@ z~6@) (and
     (= (Mul x~2@ (Add y~4@ z~6@)) (Add (Mul x~2@ y~4@) (Mul x~2@ z~6@)))
     (= (Mul (Add x~2@ y~4@) z~6@) (Add (Mul x~2@ z~6@) (Mul y~4@ z~6@)))
     (= (Mul x~2@ (Sub y~4@ z~6@)) (Sub (Mul x~2@ y~4@) (Mul x~2@ z~6@)))
     (= (Mul (Sub x~2@ y~4@) z~6@) (Sub (Mul x~2@ z~6@) (Mul y~4@ z~6@)))
   ))
   :pattern ((ens%main!nl_basics.lemma_mul_is_distributive. x~2@ y~4@ z~6@))
   :qid internal_ens__main!nl_basics.lemma_mul_is_distributive._definition
   :skolemid skolem_internal_ens__main!nl_basics.lemma_mul_is_distributive._definition
)))

;; Function-Def main::inst_0
;; mariposa_data/v_nl//15771138493408377483/nlqi_verus/src/main.rs:7:1: 26:40 (#0)
(push)
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
 (declare-const temp_0_0~309@ Int)
 (declare-const temp_0_1~458@ Int)
 (declare-const temp_1_0~607@ Int)
 (declare-const temp_1_1~728@ Int)
 (declare-const temp_2_0~865@ Int)
 (declare-const temp_2_1~966@ Int)
 (declare-const temp_3_0~1111@ Int)
 (declare-const temp_3_1~1244@ Int)
 (declare-const temp_4_0~1431@ Int)
 (declare-const temp_4_1~1568@ Int)
 (declare-const temp_5_0~1841@ Int)
 (declare-const temp_5_1~1966@ Int)
 (declare-const temp_6_0~2121@ Int)
 (declare-const temp_6_1~2242@ Int)
 (declare-const temp_7_0~2511@ Int)
 (declare-const temp_7_1~2640@ Int)
 (declare-const temp_8_0~2793@ Int)
 (declare-const temp_8_1~2918@ Int)
 (declare-const temp_9_0~3109@ Int)
 (declare-const temp_9_1~3218@ Int)
 (declare-const temp_10_0~3371@ Int)
 (declare-const temp_10_1~3496@ Int)
 (declare-const temp_11_0~3615@ Int)
 (declare-const temp_11_1~3704@ Int)
 (declare-const temp_12_0~3865@ Int)
 (declare-const temp_12_1~3998@ Int)
 (declare-const temp_13_0~4165@ Int)
 (declare-const temp_13_1~4286@ Int)
 (declare-const temp_14_0~4419@ Int)
 (declare-const temp_14_1~4524@ Int)
 (declare-const temp_15_0~4687@ Int)
 (declare-const temp_15_1~4816@ Int)
 (declare-const temp_16_0~4969@ Int)
 (declare-const temp_16_1~5094@ Int)
 (assert
  fuel_defaults
 )
 ;; assertion failed
 (declare-const %%location_label%%0 Bool)
 ;; assertion failed
 (declare-const %%location_label%%1 Bool)
 ;; assertion failed
 (declare-const %%location_label%%2 Bool)
 ;; assertion failed
 (declare-const %%location_label%%3 Bool)
 ;; assertion failed
 (declare-const %%location_label%%4 Bool)
 ;; assertion failed
 (declare-const %%location_label%%5 Bool)
 ;; assertion failed
 (declare-const %%location_label%%6 Bool)
 ;; assertion failed
 (declare-const %%location_label%%7 Bool)
 ;; assertion failed
 (declare-const %%location_label%%8 Bool)
 ;; assertion failed
 (declare-const %%location_label%%9 Bool)
 ;; assertion failed
 (declare-const %%location_label%%10 Bool)
 ;; assertion failed
 (declare-const %%location_label%%11 Bool)
 ;; assertion failed
 (declare-const %%location_label%%12 Bool)
 ;; assertion failed
 (declare-const %%location_label%%13 Bool)
 ;; assertion failed
 (declare-const %%location_label%%14 Bool)
 ;; assertion failed
 (declare-const %%location_label%%15 Bool)
 ;; assertion failed
 (declare-const %%location_label%%16 Bool)
 (declare-const %%query%% Bool)
 (assert
  (=>
   %%query%%
   (not (=>
     (= temp_0_0~309@ (Mul (Mul (Mul (Mul (Mul a0~2@ a0~2@) (Mul c0~6@ b0~4@)) (Mul (Mul b0~4@
           a0~2@
          ) (Mul c0~6@ a0~2@)
         )
        ) (Sub (Mul (Mul d0~8@ a0~2@) (Mul a0~2@ b0~4@)) (Mul b0~4@ (Add a0~2@ d0~8@)))
       ) (Mul (Mul (Mul (Sub b0~4@ d0~8@) (Sub c0~6@ d0~8@)) (Mul (Mul b0~4@ a0~2@) (Sub b0~4@
           c0~6@
         ))
        ) (Add (Mul (Sub 87 a0~2@) (Mul c0~6@ d0~8@)) (Mul (Mul a0~2@ 80) (Mul c0~6@ b0~4@)))
     )))
     (=>
      (= temp_0_1~458@ (Mul (Mul (Mul (Mul (Mul a0~2@ a0~2@) (Mul c0~6@ b0~4@)) (Mul (Mul b0~4@
            a0~2@
           ) (Mul c0~6@ a0~2@)
          )
         ) (Sub (Mul (Mul d0~8@ a0~2@) (Mul a0~2@ b0~4@)) (Mul b0~4@ (Add a0~2@ d0~8@)))
        ) (Mul (Mul (Mul (Sub b0~4@ d0~8@) (Sub c0~6@ d0~8@)) (Mul (Mul b0~4@ a0~2@) (Sub b0~4@
            c0~6@
          ))
         ) (Add (Mul (Sub 87 a0~2@) (Mul c0~6@ d0~8@)) (Mul (Mul a0~2@ 80) (Mul b0~4@ c0~6@)))
      )))
      (and
       (=>
        (ens%main!nl_basics.lemma_mul_is_commutative. c0~6@ b0~4@)
        (=>
         %%location_label%%0
         (= temp_0_0~309@ temp_0_1~458@)
       ))
       (=>
        (= temp_0_0~309@ temp_0_1~458@)
        (=>
         (= temp_1_0~607@ (Mul (Mul (Mul (Mul (Mul b1~12@ c1~14@) (Mul c1~14@ b1~12@)) (Mul (Sub
               b1~12@ a1~10@
              ) (Mul d1~16@ a1~10@)
             )
            ) (Mul (Mul (Mul 75 a1~10@) (Mul c1~14@ b1~12@)) (Mul (Mul c1~14@ c1~14@) (Mul d1~16@
               b1~12@
            )))
           ) (Mul (Mul d1~16@ (Sub (Mul c1~14@ c1~14@) (Mul d1~16@ c1~14@))) (Sub (Mul (Mul d1~16@
               c1~14@
              ) (Mul b1~12@ b1~12@)
             ) (Mul c1~14@ a1~10@)
         ))))
         (=>
          (= temp_1_1~728@ (Mul (Mul (Mul (Mul (Mul b1~12@ c1~14@) (Mul c1~14@ b1~12@)) (Mul (Sub
                b1~12@ a1~10@
               ) (Mul d1~16@ a1~10@)
              )
             ) (Mul (Mul (Mul 75 a1~10@) (Mul c1~14@ b1~12@)) (Mul (Mul d1~16@ b1~12@) (Mul c1~14@
                c1~14@
             )))
            ) (Mul (Mul d1~16@ (Sub (Mul c1~14@ c1~14@) (Mul d1~16@ c1~14@))) (Sub (Mul (Mul d1~16@
                c1~14@
               ) (Mul b1~12@ b1~12@)
              ) (Mul c1~14@ a1~10@)
          ))))
          (and
           (=>
            (= tmp%1@ (Mul c1~14@ c1~14@))
            (=>
             (= tmp%2@ (Mul d1~16@ b1~12@))
             (=>
              (ens%main!nl_basics.lemma_mul_is_commutative. tmp%1@ tmp%2@)
              (=>
               %%location_label%%1
               (= temp_1_0~607@ temp_1_1~728@)
           ))))
           (=>
            (= temp_1_0~607@ temp_1_1~728@)
            (=>
             (= temp_2_0~865@ (Mul (Add (Sub (Mul (Sub c2~22@ b2~20@) (Mul b2~20@ c2~22@)) (Mul (Add
                   c2~22@ a2~18@
                  ) b2~20@
                 )
                ) (Mul (Mul (Add c2~22@ b2~20@) (Mul b2~20@ b2~20@)) d2~24@)
               ) (Mul (Mul (Mul (Mul c2~22@ b2~20@) (Add d2~24@ a2~18@)) (Mul (Mul c2~22@ d2~24@) (
                   Mul c2~22@ a2~18@
                 ))
                ) (Mul a2~18@ (Mul (Mul b2~20@ b2~20@) (Add a2~18@ c2~22@)))
             )))
             (=>
              (= temp_2_1~966@ (Mul (Add (Sub (Mul (Sub c2~22@ b2~20@) (Mul b2~20@ c2~22@)) (Mul (Add
                    c2~22@ a2~18@
                   ) b2~20@
                  )
                 ) (Mul (Mul (Add c2~22@ b2~20@) (Mul b2~20@ b2~20@)) d2~24@)
                ) (Mul (Mul (Mul (Mul c2~22@ b2~20@) (Add d2~24@ a2~18@)) (Mul (Mul c2~22@ d2~24@) (
                    Mul c2~22@ a2~18@
                  ))
                 ) (Mul a2~18@ (Mul (Mul b2~20@ b2~20@) (Add a2~18@ c2~22@)))
              )))
              (and
               (=>
                (ens%main!nl_basics.lemma_mul_is_commutative. b2~20@ b2~20@)
                (=>
                 %%location_label%%2
                 (= temp_2_0~865@ temp_2_1~966@)
               ))
               (=>
                (= temp_2_0~865@ temp_2_1~966@)
                (=>
                 (= temp_3_0~1111@ (Mul (Sub (Mul (Mul (Mul a3~26@ d3~32@) (Mul c3~30@ d3~32@)) (Sub (Mul
                       a3~26@ d3~32@
                      ) (Mul d3~32@ b3~28@)
                     )
                    ) (Mul (Mul (Add a3~26@ d3~32@) (Mul c3~30@ a3~26@)) (Add (Mul d3~32@ a3~26@) (Mul d3~32@
                       c3~30@
                    )))
                   ) (Mul (Mul (Sub (Mul c3~30@ c3~30@) a3~26@) (Mul d3~32@ (Mul d3~32@ d3~32@))) (Mul
                     (Mul b3~28@ (Mul b3~28@ b3~28@)) (Mul (Add d3~32@ a3~26@) (Add b3~28@ b3~28@))
                 ))))
                 (=>
                  (= temp_3_1~1244@ (Mul (Sub (Mul (Mul (Mul a3~26@ d3~32@) (Mul c3~30@ d3~32@)) (Sub (Mul
                        a3~26@ d3~32@
                       ) (Mul d3~32@ b3~28@)
                      )
                     ) (Add (Mul (Mul (Add a3~26@ d3~32@) (Mul c3~30@ a3~26@)) (Mul d3~32@ a3~26@)) (Mul
                       (Mul (Add a3~26@ d3~32@) (Mul c3~30@ a3~26@)) (Mul d3~32@ c3~30@)
                     ))
                    ) (Mul (Mul (Sub (Mul c3~30@ c3~30@) a3~26@) (Mul d3~32@ (Mul d3~32@ d3~32@))) (Mul
                      (Mul b3~28@ (Mul b3~28@ b3~28@)) (Mul (Add d3~32@ a3~26@) (Add b3~28@ b3~28@))
                  ))))
                  (and
                   (=>
                    (= tmp%3@ (Mul (Add a3~26@ d3~32@) (Mul c3~30@ a3~26@)))
                    (=>
                     (= tmp%4@ (Mul d3~32@ a3~26@))
                     (=>
                      (= tmp%5@ (Mul d3~32@ c3~30@))
                      (=>
                       (ens%main!nl_basics.lemma_mul_is_distributive. tmp%3@ tmp%4@ tmp%5@)
                       (=>
                        %%location_label%%3
                        (= temp_3_0~1111@ temp_3_1~1244@)
                   )))))
                   (=>
                    (= temp_3_0~1111@ temp_3_1~1244@)
                    (=>
                     (= temp_4_0~1431@ (Mul (Mul (Mul (Mul (Mul a4~34@ d4~40@) (Mul d4~40@ c4~38@)) (Sub (Mul
                           b4~36@ c4~38@
                          ) (Mul d4~40@ b4~36@)
                         )
                        ) (Mul (Mul (Mul d4~40@ c4~38@) (Mul a4~34@ b4~36@)) (Add (Mul b4~36@ a4~34@) (Mul d4~40@
                           b4~36@
                        )))
                       ) (Mul (Mul (Mul (Mul c4~38@ 98) (Mul d4~40@ a4~34@)) (Mul c4~38@ (Mul d4~40@ a4~34@)))
                        (Mul (Sub (Mul d4~40@ d4~40@) (Add a4~34@ d4~40@)) (Mul (Sub a4~34@ c4~38@) (Add c4~38@
                           b4~36@
                     ))))))
                     (=>
                      (= temp_4_1~1568@ (Mul (Mul (Mul (Mul (Mul c4~38@ 98) (Mul d4~40@ a4~34@)) (Mul c4~38@
                           (Mul d4~40@ a4~34@)
                          )
                         ) (Mul (Sub (Mul d4~40@ d4~40@) (Add a4~34@ d4~40@)) (Mul (Sub a4~34@ c4~38@) (Add c4~38@
                            b4~36@
                         )))
                        ) (Mul (Mul (Mul (Mul a4~34@ d4~40@) (Mul d4~40@ c4~38@)) (Sub (Mul b4~36@ c4~38@) (
                            Mul d4~40@ b4~36@
                          ))
                         ) (Mul (Mul (Mul d4~40@ c4~38@) (Mul a4~34@ b4~36@)) (Add (Mul b4~36@ a4~34@) (Mul d4~40@
                            b4~36@
                      ))))))
                      (and
                       (=>
                        (= tmp%6@ (Mul (Mul (Mul (Mul a4~34@ d4~40@) (Mul d4~40@ c4~38@)) (Sub (Mul b4~36@ c4~38@)
                            (Mul d4~40@ b4~36@)
                           )
                          ) (Mul (Mul (Mul d4~40@ c4~38@) (Mul a4~34@ b4~36@)) (Add (Mul b4~36@ a4~34@) (Mul d4~40@
                             b4~36@
                        )))))
                        (=>
                         (= tmp%7@ (Mul (Mul (Mul (Mul c4~38@ 98) (Mul d4~40@ a4~34@)) (Mul c4~38@ (Mul d4~40@
                              a4~34@
                            ))
                           ) (Mul (Sub (Mul d4~40@ d4~40@) (Add a4~34@ d4~40@)) (Mul (Sub a4~34@ c4~38@) (Add c4~38@
                              b4~36@
                         )))))
                         (=>
                          (ens%main!nl_basics.lemma_mul_is_commutative. tmp%6@ tmp%7@)
                          (=>
                           %%location_label%%4
                           (= temp_4_0~1431@ temp_4_1~1568@)
                       ))))
                       (=>
                        (= temp_4_0~1431@ temp_4_1~1568@)
                        (=>
                         (= temp_5_0~1841@ (Mul (Mul (Mul (Mul (Sub d5~48@ c5~46@) (Mul d5~48@ a5~42@)) (Mul (Mul
                               d5~48@ b5~44@
                              ) (Mul a5~42@ c5~46@)
                             )
                            ) (Mul a5~42@ (Mul (Mul a5~42@ c5~46@) (Mul a5~42@ a5~42@)))
                           ) (Sub (Mul (Mul (Mul d5~48@ b5~44@) (Add d5~48@ c5~46@)) (Mul (Sub a5~42@ c5~46@) (
                               Mul b5~44@ c5~46@
                             ))
                            ) (Mul (Sub (Sub c5~46@ b5~44@) (Mul c5~46@ d5~48@)) (Mul (Add c5~46@ a5~42@) (Mul a5~42@
                               a5~42@
                         ))))))
                         (=>
                          (= temp_5_1~1966@ (Mul (Mul (Mul (Mul (Sub d5~48@ c5~46@) (Mul d5~48@ a5~42@)) (Mul (Mul
                                d5~48@ b5~44@
                               ) (Mul a5~42@ c5~46@)
                              )
                             ) (Mul a5~42@ (Mul (Mul a5~42@ c5~46@) (Mul a5~42@ a5~42@)))
                            ) (Sub (Mul (Add (Mul (Mul d5~48@ b5~44@) d5~48@) (Mul (Mul d5~48@ b5~44@) c5~46@))
                              (Mul (Sub a5~42@ c5~46@) (Mul b5~44@ c5~46@))
                             ) (Mul (Sub (Sub c5~46@ b5~44@) (Mul c5~46@ d5~48@)) (Mul (Add c5~46@ a5~42@) (Mul a5~42@
                                a5~42@
                          ))))))
                          (and
                           (=>
                            (= tmp%8@ (Mul d5~48@ b5~44@))
                            (=>
                             (ens%main!nl_basics.lemma_mul_is_distributive. tmp%8@ d5~48@ c5~46@)
                             (=>
                              %%location_label%%5
                              (= temp_5_0~1841@ temp_5_1~1966@)
                           )))
                           (=>
                            (= temp_5_0~1841@ temp_5_1~1966@)
                            (=>
                             (= temp_6_0~2121@ (Mul (Mul (Mul (Mul (Add b6~52@ d6~56@) (Mul a6~50@ c6~54@)) (Mul (Add
                                   c6~54@ a6~50@
                                  ) (Sub c6~54@ d6~56@)
                                 )
                                ) (Mul (Mul a6~50@ d6~56@) (Mul (Mul a6~50@ d6~56@) (Add c6~54@ a6~50@)))
                               ) (Mul (Mul (Mul (Mul c6~54@ d6~56@) (Sub d6~56@ a6~50@)) (Mul (Add c6~54@ d6~56@) (
                                   Mul d6~56@ c6~54@
                                 ))
                                ) (Mul (Mul (Mul b6~52@ c6~54@) (Mul b6~52@ a6~50@)) (Mul (Mul b6~52@ c6~54@) (Mul d6~56@
                                   c6~54@
                             ))))))
                             (=>
                              (= temp_6_1~2242@ (Mul (Mul (Mul (Mul (Mul c6~54@ d6~56@) (Sub d6~56@ a6~50@)) (Mul (Add
                                    c6~54@ d6~56@
                                   ) (Mul d6~56@ c6~54@)
                                  )
                                 ) (Mul (Mul (Mul b6~52@ c6~54@) (Mul b6~52@ a6~50@)) (Mul (Mul b6~52@ c6~54@) (Mul d6~56@
                                    c6~54@
                                 )))
                                ) (Mul (Mul (Mul (Add b6~52@ d6~56@) (Mul a6~50@ c6~54@)) (Mul (Add c6~54@ a6~50@) (
                                    Sub c6~54@ d6~56@
                                  ))
                                 ) (Mul (Mul a6~50@ d6~56@) (Mul (Mul a6~50@ d6~56@) (Add c6~54@ a6~50@)))
                              )))
                              (and
                               (=>
                                (= tmp%9@ (Mul (Mul (Mul (Add b6~52@ d6~56@) (Mul a6~50@ c6~54@)) (Mul (Add c6~54@ a6~50@)
                                    (Sub c6~54@ d6~56@)
                                   )
                                  ) (Mul (Mul a6~50@ d6~56@) (Mul (Mul a6~50@ d6~56@) (Add c6~54@ a6~50@)))
                                ))
                                (=>
                                 (= tmp%10@ (Mul (Mul (Mul (Mul c6~54@ d6~56@) (Sub d6~56@ a6~50@)) (Mul (Add c6~54@ d6~56@)
                                     (Mul d6~56@ c6~54@)
                                    )
                                   ) (Mul (Mul (Mul b6~52@ c6~54@) (Mul b6~52@ a6~50@)) (Mul (Mul b6~52@ c6~54@) (Mul d6~56@
                                      c6~54@
                                 )))))
                                 (=>
                                  (ens%main!nl_basics.lemma_mul_is_commutative. tmp%9@ tmp%10@)
                                  (=>
                                   %%location_label%%6
                                   (= temp_6_0~2121@ temp_6_1~2242@)
                               ))))
                               (=>
                                (= temp_6_0~2121@ temp_6_1~2242@)
                                (=>
                                 (= temp_7_0~2511@ (Add (Mul (Add (Add (Mul d7~64@ d7~64@) (Mul a7~58@ b7~60@)) (Mul (Mul
                                       c7~62@ c7~62@
                                      ) (Mul c7~62@ c7~62@)
                                     )
                                    ) (Mul (Mul (Add a7~58@ a7~58@) (Mul b7~60@ c7~62@)) (Mul (Mul b7~60@ b7~60@) (Mul b7~60@
                                       c7~62@
                                    )))
                                   ) (Mul (Mul (Mul (Mul c7~62@ b7~60@) (Add b7~60@ a7~58@)) (Mul (Sub d7~64@ c7~62@) (
                                       Mul a7~58@ c7~62@
                                     ))
                                    ) (Mul (Mul (Add b7~60@ d7~64@) (Mul c7~62@ a7~58@)) (Sub (Mul d7~64@ c7~62@) (Mul b7~60@
                                       b7~60@
                                 ))))))
                                 (=>
                                  (= temp_7_1~2640@ (Add (Mul (Add (Add (Mul d7~64@ d7~64@) (Mul a7~58@ b7~60@)) (Mul (Mul
                                        c7~62@ c7~62@
                                       ) (Mul c7~62@ c7~62@)
                                      )
                                     ) (Mul (Mul (Add a7~58@ a7~58@) (Mul b7~60@ c7~62@)) (Mul (Mul b7~60@ b7~60@) (Mul b7~60@
                                        c7~62@
                                     )))
                                    ) (Mul (Mul (Mul (Mul c7~62@ b7~60@) (Add b7~60@ a7~58@)) (Mul (Sub d7~64@ c7~62@) (
                                        Mul a7~58@ c7~62@
                                      ))
                                     ) (Mul (Mul (Add b7~60@ d7~64@) (Mul c7~62@ a7~58@)) (Sub (Mul c7~62@ d7~64@) (Mul b7~60@
                                        b7~60@
                                  ))))))
                                  (and
                                   (=>
                                    (ens%main!nl_basics.lemma_mul_is_commutative. d7~64@ c7~62@)
                                    (=>
                                     %%location_label%%7
                                     (= temp_7_0~2511@ temp_7_1~2640@)
                                   ))
                                   (=>
                                    (= temp_7_0~2511@ temp_7_1~2640@)
                                    (=>
                                     (= temp_8_0~2793@ (Mul (Mul (Add (Mul c8~70@ (Sub b8~68@ a8~66@)) (Sub (Mul a8~66@ c8~70@)
                                          (Mul b8~68@ d8~72@)
                                         )
                                        ) (Mul (Mul (Mul a8~66@ d8~72@) (Mul c8~70@ c8~70@)) (Mul (Mul a8~66@ c8~70@) (Mul b8~68@
                                           c8~70@
                                        )))
                                       ) (Mul (Mul (Sub (Mul a8~66@ b8~68@) (Mul d8~72@ a8~66@)) (Mul (Mul c8~70@ d8~72@) (
                                           Sub c8~70@ b8~68@
                                         ))
                                        ) (Add (Add (Mul a8~66@ b8~68@) (Add d8~72@ c8~70@)) (Mul (Mul b8~68@ d8~72@) (Sub a8~66@
                                           c8~70@
                                     ))))))
                                     (=>
                                      (= temp_8_1~2918@ (Mul (Mul (Add (Mul c8~70@ (Sub b8~68@ a8~66@)) (Sub (Mul a8~66@ c8~70@)
                                           (Mul b8~68@ d8~72@)
                                          )
                                         ) (Mul (Mul (Mul a8~66@ d8~72@) (Mul c8~70@ c8~70@)) (Mul (Mul a8~66@ c8~70@) (Mul b8~68@
                                            c8~70@
                                         )))
                                        ) (Mul (Sub (Mul a8~66@ b8~68@) (Mul d8~72@ a8~66@)) (Mul (Mul (Mul c8~70@ d8~72@) (
                                            Sub c8~70@ b8~68@
                                           )
                                          ) (Add (Add (Mul a8~66@ b8~68@) (Add d8~72@ c8~70@)) (Mul (Mul b8~68@ d8~72@) (Sub a8~66@
                                             c8~70@
                                      )))))))
                                      (and
                                       (=>
                                        (= tmp%11@ (Sub (Mul a8~66@ b8~68@) (Mul d8~72@ a8~66@)))
                                        (=>
                                         (= tmp%12@ (Mul (Mul c8~70@ d8~72@) (Sub c8~70@ b8~68@)))
                                         (=>
                                          (= tmp%13@ (Add (Add (Mul a8~66@ b8~68@) (Add d8~72@ c8~70@)) (Mul (Mul b8~68@ d8~72@)
                                             (Sub a8~66@ c8~70@)
                                          )))
                                          (=>
                                           (ens%main!nl_basics.lemma_mul_is_associative. tmp%11@ tmp%12@ tmp%13@)
                                           (=>
                                            %%location_label%%8
                                            (= temp_8_0~2793@ temp_8_1~2918@)
                                       )))))
                                       (=>
                                        (= temp_8_0~2793@ temp_8_1~2918@)
                                        (=>
                                         (= temp_9_0~3109@ (Mul (Mul (Mul (Mul (Sub a9~74@ d9~80@) (Mul b9~76@ a9~74@)) (Mul (Sub
                                               b9~76@ d9~80@
                                              ) (Mul d9~80@ b9~76@)
                                             )
                                            ) (Mul (Mul (Add c9~78@ b9~76@) b9~76@) (Mul (Sub b9~76@ d9~80@) (Mul b9~76@ b9~76@)))
                                           ) (Mul (Mul d9~80@ (Mul (Mul d9~80@ b9~76@) (Mul d9~80@ c9~78@))) (Add (Mul (Mul c9~78@
                                               d9~80@
                                              ) (Add d9~80@ c9~78@)
                                             ) (Mul (Mul c9~78@ c9~78@) d9~80@)
                                         ))))
                                         (=>
                                          (= temp_9_1~3218@ (Mul (Mul (Mul (Mul (Sub a9~74@ d9~80@) (Mul b9~76@ a9~74@)) (Mul (Sub
                                                b9~76@ d9~80@
                                               ) (Mul d9~80@ b9~76@)
                                              )
                                             ) (Mul (Mul (Add c9~78@ b9~76@) b9~76@) (Mul (Sub b9~76@ d9~80@) (Mul b9~76@ b9~76@)))
                                            ) (Mul (Mul d9~80@ (Mul (Mul d9~80@ b9~76@) (Mul d9~80@ c9~78@))) (Add (Mul (Mul c9~78@
                                                d9~80@
                                               ) (Add d9~80@ c9~78@)
                                              ) (Mul (Mul c9~78@ c9~78@) d9~80@)
                                          ))))
                                          (and
                                           (=>
                                            (ens%main!nl_basics.lemma_mul_is_commutative. b9~76@ b9~76@)
                                            (=>
                                             %%location_label%%9
                                             (= temp_9_0~3109@ temp_9_1~3218@)
                                           ))
                                           (=>
                                            (= temp_9_0~3109@ temp_9_1~3218@)
                                            (=>
                                             (= temp_10_0~3371@ (Mul (Mul (Mul (Mul (Mul a10~82@ a10~82@) (Mul d10~88@ c10~86@)) (
                                                  Sub (Mul c10~86@ b10~84@) (Mul a10~82@ c10~86@)
                                                 )
                                                ) (Mul (Mul (Mul a10~82@ c10~86@) b10~84@) (Mul (Mul c10~86@ c10~86@) (Mul c10~86@ a10~82@)))
                                               ) (Mul (Mul (Add (Mul a10~82@ d10~88@) (Mul a10~82@ b10~84@)) (Mul (Mul b10~84@ b10~84@)
                                                  (Mul b10~84@ c10~86@)
                                                 )
                                                ) (Mul (Mul (Mul d10~88@ c10~86@) (Mul c10~86@ d10~88@)) (Mul (Mul d10~88@ b10~84@)
                                                  (Add a10~82@ b10~84@)
                                             )))))
                                             (=>
                                              (= temp_10_1~3496@ (Mul (Mul (Mul (Mul (Mul a10~82@ a10~82@) (Mul d10~88@ c10~86@)) (
                                                   Sub (Mul c10~86@ b10~84@) (Mul a10~82@ c10~86@)
                                                  )
                                                 ) (Mul (Mul a10~82@ (Mul c10~86@ b10~84@)) (Mul (Mul c10~86@ c10~86@) (Mul c10~86@ a10~82@)))
                                                ) (Mul (Mul (Add (Mul a10~82@ d10~88@) (Mul a10~82@ b10~84@)) (Mul (Mul b10~84@ b10~84@)
                                                   (Mul b10~84@ c10~86@)
                                                  )
                                                 ) (Mul (Mul (Mul d10~88@ c10~86@) (Mul c10~86@ d10~88@)) (Mul (Mul d10~88@ b10~84@)
                                                   (Add a10~82@ b10~84@)
                                              )))))
                                              (and
                                               (=>
                                                (ens%main!nl_basics.lemma_mul_is_associative. a10~82@ c10~86@ b10~84@)
                                                (=>
                                                 %%location_label%%10
                                                 (= temp_10_0~3371@ temp_10_1~3496@)
                                               ))
                                               (=>
                                                (= temp_10_0~3371@ temp_10_1~3496@)
                                                (=>
                                                 (= temp_11_0~3615@ (Mul (Mul (Add d11~96@ b11~92@) b11~92@) (Mul (Add (Add (Sub c11~94@
                                                       d11~96@
                                                      ) (Mul d11~96@ a11~90@)
                                                     ) (Mul (Mul a11~90@ a11~90@) (Mul b11~92@ a11~90@))
                                                    ) (Mul (Sub (Mul a11~90@ 84) (Add b11~92@ d11~96@)) (Mul (Mul c11~94@ d11~96@) (Add
                                                       c11~94@ d11~96@
                                                 ))))))
                                                 (=>
                                                  (= temp_11_1~3704@ (Mul (Mul (Add d11~96@ b11~92@) b11~92@) (Mul (Add (Add (Sub c11~94@
                                                        d11~96@
                                                       ) (Mul d11~96@ a11~90@)
                                                      ) (Mul (Mul a11~90@ a11~90@) (Mul b11~92@ a11~90@))
                                                     ) (Mul (Sub (Mul a11~90@ 84) (Add b11~92@ d11~96@)) (Mul (Mul c11~94@ d11~96@) (Add
                                                        c11~94@ d11~96@
                                                  ))))))
                                                  (and
                                                   (=>
                                                    (ens%main!nl_basics.lemma_mul_is_commutative. a11~90@ a11~90@)
                                                    (=>
                                                     %%location_label%%11
                                                     (= temp_11_0~3615@ temp_11_1~3704@)
                                                   ))
                                                   (=>
                                                    (= temp_11_0~3615@ temp_11_1~3704@)
                                                    (=>
                                                     (= temp_12_0~3865@ (Mul (Mul (Mul (Sub (Mul c12~102@ b12~100@) (Mul c12~102@ c12~102@))
                                                         (Mul (Mul c12~102@ d12~104@) c12~102@)
                                                        ) (Mul (Mul (Mul b12~100@ a12~98@) (Mul b12~100@ d12~104@)) (Mul (Mul d12~104@ c12~102@)
                                                          (Sub b12~100@ d12~104@)
                                                        ))
                                                       ) (Sub (Mul (Sub a12~98@ (Mul 4 b12~100@)) c12~102@) (Mul (Mul (Mul a12~98@ c12~102@)
                                                          (Mul b12~100@ b12~100@)
                                                         ) (Mul (Mul a12~98@ c12~102@) (Add a12~98@ 76))
                                                     ))))
                                                     (=>
                                                      (= temp_12_1~3998@ (Mul (Mul (Mul (Mul (Sub (Mul c12~102@ b12~100@) (Mul c12~102@ c12~102@))
                                                           (Mul c12~102@ d12~104@)
                                                          ) c12~102@
                                                         ) (Mul (Mul (Mul b12~100@ a12~98@) (Mul b12~100@ d12~104@)) (Mul (Mul d12~104@ c12~102@)
                                                           (Sub b12~100@ d12~104@)
                                                         ))
                                                        ) (Sub (Mul (Sub a12~98@ (Mul 4 b12~100@)) c12~102@) (Mul (Mul (Mul a12~98@ c12~102@)
                                                           (Mul b12~100@ b12~100@)
                                                          ) (Mul (Mul a12~98@ c12~102@) (Add a12~98@ 76))
                                                      ))))
                                                      (and
                                                       (=>
                                                        (= tmp%14@ (Sub (Mul c12~102@ b12~100@) (Mul c12~102@ c12~102@)))
                                                        (=>
                                                         (= tmp%15@ (Mul c12~102@ d12~104@))
                                                         (=>
                                                          (ens%main!nl_basics.lemma_mul_is_associative. tmp%14@ tmp%15@ c12~102@)
                                                          (=>
                                                           %%location_label%%12
                                                           (= temp_12_0~3865@ temp_12_1~3998@)
                                                       ))))
                                                       (=>
                                                        (= temp_12_0~3865@ temp_12_1~3998@)
                                                        (=>
                                                         (= temp_13_0~4165@ (Mul (Mul c13~110@ (Mul (Add (Mul d13~112@ b13~108@) (Mul c13~110@ d13~112@))
                                                             (Sub a13~106@ (Mul a13~106@ c13~110@))
                                                            )
                                                           ) (Sub (Mul (Mul (Sub d13~112@ 34) (Mul b13~108@ b13~108@)) (Mul (Mul b13~108@ b13~108@)
                                                              (Mul 48 d13~112@)
                                                             )
                                                            ) (Mul (Add (Mul c13~110@ d13~112@) (Mul a13~106@ b13~108@)) (Mul (Add c13~110@ d13~112@)
                                                              (Mul a13~106@ c13~110@)
                                                         )))))
                                                         (=>
                                                          (= temp_13_1~4286@ (Mul (Mul c13~110@ (Mul (Add (Mul d13~112@ b13~108@) (Mul c13~110@ d13~112@))
                                                              (Sub a13~106@ (Mul a13~106@ c13~110@))
                                                             )
                                                            ) (Sub (Mul (Mul (Sub d13~112@ 34) (Mul b13~108@ b13~108@)) (Mul (Mul b13~108@ b13~108@)
                                                               (Mul 48 d13~112@)
                                                              )
                                                             ) (Mul (Add (Mul c13~110@ d13~112@) (Mul a13~106@ b13~108@)) (Mul (Mul a13~106@ c13~110@)
                                                               (Add c13~110@ d13~112@)
                                                          )))))
                                                          (and
                                                           (=>
                                                            (= tmp%16@ (Add c13~110@ d13~112@))
                                                            (=>
                                                             (= tmp%17@ (Mul a13~106@ c13~110@))
                                                             (=>
                                                              (ens%main!nl_basics.lemma_mul_is_commutative. tmp%16@ tmp%17@)
                                                              (=>
                                                               %%location_label%%13
                                                               (= temp_13_0~4165@ temp_13_1~4286@)
                                                           ))))
                                                           (=>
                                                            (= temp_13_0~4165@ temp_13_1~4286@)
                                                            (=>
                                                             (= temp_14_0~4419@ (Mul (Sub (Sub (Add (Mul d14~120@ c14~118@) (Mul d14~120@ d14~120@))
                                                                 (Mul (Mul b14~116@ b14~116@) (Mul a14~114@ b14~116@))
                                                                ) (Mul (Sub c14~118@ (Mul c14~118@ a14~114@)) (Mul d14~120@ (Mul a14~114@ c14~118@)))
                                                               ) (Mul (Mul (Mul (Mul b14~116@ a14~114@) (Mul b14~116@ c14~118@)) (Mul (Sub d14~120@
                                                                   a14~114@
                                                                  ) (Mul a14~114@ a14~114@)
                                                                 )
                                                                ) (Sub c14~118@ c14~118@)
                                                             )))
                                                             (=>
                                                              (= temp_14_1~4524@ (Mul (Sub (Sub (Add (Mul d14~120@ c14~118@) (Mul d14~120@ d14~120@))
                                                                  (Mul (Mul b14~116@ b14~116@) (Mul a14~114@ b14~116@))
                                                                 ) (Mul (Sub c14~118@ (Mul c14~118@ a14~114@)) (Mul d14~120@ (Mul a14~114@ c14~118@)))
                                                                ) (Mul (Mul (Mul (Mul b14~116@ a14~114@) (Mul b14~116@ c14~118@)) (Sub (Mul d14~120@
                                                                    (Mul a14~114@ a14~114@)
                                                                   ) (Mul a14~114@ (Mul a14~114@ a14~114@))
                                                                  )
                                                                 ) (Sub c14~118@ c14~118@)
                                                              )))
                                                              (and
                                                               (=>
                                                                (= tmp%18@ (Mul a14~114@ a14~114@))
                                                                (=>
                                                                 (ens%main!nl_basics.lemma_mul_is_distributive. d14~120@ a14~114@ tmp%18@)
                                                                 (=>
                                                                  %%location_label%%14
                                                                  (= temp_14_0~4419@ temp_14_1~4524@)
                                                               )))
                                                               (=>
                                                                (= temp_14_0~4419@ temp_14_1~4524@)
                                                                (=>
                                                                 (= temp_15_0~4687@ (Mul (Mul (Mul (Mul (Add c15~126@ a15~122@) (Sub c15~126@ d15~128@))
                                                                     (Mul (Mul d15~128@ b15~124@) (Mul b15~124@ a15~122@))
                                                                    ) (Add (Mul (Mul a15~122@ d15~128@) (Add a15~122@ a15~122@)) (Sub (Mul a15~122@ c15~126@)
                                                                      (Mul d15~128@ b15~124@)
                                                                    ))
                                                                   ) (Mul (Mul (Mul (Mul c15~126@ d15~128@) (Mul d15~128@ b15~124@)) (Sub (Mul b15~124@
                                                                       d15~128@
                                                                      ) (Mul d15~128@ d15~128@)
                                                                     )
                                                                    ) (Mul (Mul (Mul b15~124@ b15~124@) (Mul a15~122@ a15~122@)) (Mul (Mul c15~126@ d15~128@)
                                                                      (Mul d15~128@ b15~124@)
                                                                 )))))
                                                                 (=>
                                                                  (= temp_15_1~4816@ (Mul (Mul (Mul (Mul (Add c15~126@ a15~122@) (Sub c15~126@ d15~128@))
                                                                      (Mul (Mul d15~128@ b15~124@) (Mul b15~124@ a15~122@))
                                                                     ) (Add (Mul (Mul a15~122@ d15~128@) (Add a15~122@ a15~122@)) (Sub (Mul a15~122@ c15~126@)
                                                                       (Mul d15~128@ b15~124@)
                                                                     ))
                                                                    ) (Mul (Mul (Mul (Mul c15~126@ d15~128@) (Mul b15~124@ d15~128@)) (Sub (Mul b15~124@
                                                                        d15~128@
                                                                       ) (Mul d15~128@ d15~128@)
                                                                      )
                                                                     ) (Mul (Mul (Mul b15~124@ b15~124@) (Mul a15~122@ a15~122@)) (Mul (Mul c15~126@ d15~128@)
                                                                       (Mul d15~128@ b15~124@)
                                                                  )))))
                                                                  (and
                                                                   (=>
                                                                    (ens%main!nl_basics.lemma_mul_is_commutative. d15~128@ b15~124@)
                                                                    (=>
                                                                     %%location_label%%15
                                                                     (= temp_15_0~4687@ temp_15_1~4816@)
                                                                   ))
                                                                   (=>
                                                                    (= temp_15_0~4687@ temp_15_1~4816@)
                                                                    (=>
                                                                     (= temp_16_0~4969@ (Mul (Mul (Mul (Mul (Mul d16~136@ b16~132@) (Mul b16~132@ a16~130@))
                                                                         (Sub (Mul a16~130@ a16~130@) (Mul a16~130@ b16~132@))
                                                                        ) (Sub (Mul (Mul b16~132@ b16~132@) (Mul b16~132@ c16~134@)) (Mul (Sub d16~136@ b16~132@)
                                                                          (Mul c16~134@ c16~134@)
                                                                        ))
                                                                       ) (Mul (Mul (Sub (Add d16~136@ a16~130@) (Mul d16~136@ b16~132@)) (Mul (Sub c16~134@
                                                                           a16~130@
                                                                          ) a16~130@
                                                                         )
                                                                        ) (Mul (Sub (Mul b16~132@ d16~136@) (Mul c16~134@ b16~132@)) (Mul (Mul a16~130@ c16~134@)
                                                                          (Add d16~136@ c16~134@)
                                                                     )))))
                                                                     (=>
                                                                      (= temp_16_1~5094@ (Mul (Mul (Mul (Mul (Mul b16~132@ a16~130@) (Mul d16~136@ b16~132@))
                                                                          (Sub (Mul a16~130@ a16~130@) (Mul a16~130@ b16~132@))
                                                                         ) (Sub (Mul (Mul b16~132@ b16~132@) (Mul b16~132@ c16~134@)) (Mul (Sub d16~136@ b16~132@)
                                                                           (Mul c16~134@ c16~134@)
                                                                         ))
                                                                        ) (Mul (Mul (Sub (Add d16~136@ a16~130@) (Mul d16~136@ b16~132@)) (Mul (Sub c16~134@
                                                                            a16~130@
                                                                           ) a16~130@
                                                                          )
                                                                         ) (Mul (Sub (Mul b16~132@ d16~136@) (Mul c16~134@ b16~132@)) (Mul (Mul a16~130@ c16~134@)
                                                                           (Add d16~136@ c16~134@)
                                                                      )))))
                                                                      (=>
                                                                       (= tmp%19@ (Mul d16~136@ b16~132@))
                                                                       (=>
                                                                        (= tmp%20@ (Mul b16~132@ a16~130@))
                                                                        (=>
                                                                         (ens%main!nl_basics.lemma_mul_is_commutative. tmp%19@ tmp%20@)
                                                                         (=>
                                                                          %%location_label%%16
                                                                          (= temp_16_0~4969@ temp_16_1~5094@)
 )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
 (get-info :version)
 (assert
  %%query%%
 )
 (set-option :rlimit 4294967295)
 (check-sat)
 (set-option :rlimit 0)
(pop)
