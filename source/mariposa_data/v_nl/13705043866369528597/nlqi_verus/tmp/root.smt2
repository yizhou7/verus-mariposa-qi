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
;; mariposa_data/v_nl//13705043866369528597/nlqi_verus/src/main.rs:7:1: 26:40 (#0)
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
 (declare-const temp_0_0~297@ Int)
 (declare-const temp_0_1~434@ Int)
 (declare-const temp_1_0~571@ Int)
 (declare-const temp_1_1~680@ Int)
 (declare-const temp_2_0~855@ Int)
 (declare-const temp_2_1~964@ Int)
 (declare-const temp_3_0~1121@ Int)
 (declare-const temp_3_1~1250@ Int)
 (declare-const temp_4_0~1367@ Int)
 (declare-const temp_4_1~1456@ Int)
 (declare-const temp_5_0~1637@ Int)
 (declare-const temp_5_1~1790@ Int)
 (declare-const temp_6_0~2063@ Int)
 (declare-const temp_6_1~2164@ Int)
 (declare-const temp_7_0~2313@ Int)
 (declare-const temp_7_1~2422@ Int)
 (declare-const temp_8_0~2599@ Int)
 (declare-const temp_8_1~2732@ Int)
 (declare-const temp_9_0~2821@ Int)
 (declare-const temp_9_1~2882@ Int)
 (declare-const temp_10_0~3001@ Int)
 (declare-const temp_10_1~3074@ Int)
 (declare-const temp_11_0~3187@ Int)
 (declare-const temp_11_1~3248@ Int)
 (declare-const temp_12_0~3413@ Int)
 (declare-const temp_12_1~3566@ Int)
 (declare-const temp_13_0~3765@ Int)
 (declare-const temp_13_1~3938@ Int)
 (declare-const temp_14_0~4149@ Int)
 (declare-const temp_14_1~4274@ Int)
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
 (declare-const %%query%% Bool)
 (assert
  (=>
   %%query%%
   (not (=>
     (= temp_0_0~297@ (Mul (Mul (Mul (Mul (Mul a0~2@ b0~4@) (Mul d0~8@ c0~6@)) (Mul (Mul d0~8@
           c0~6@
          ) (Mul d0~8@ c0~6@)
         )
        ) (Mul (Mul (Mul b0~4@ d0~8@) (Mul c0~6@ b0~4@)) (Mul (Mul c0~6@ 84) c0~6@))
       ) (Mul (Mul (Add (Mul a0~2@ d0~8@) (Mul d0~8@ c0~6@)) (Mul (Mul b0~4@ a0~2@) (Mul c0~6@
           b0~4@
         ))
        ) (Mul (Mul (Mul c0~6@ c0~6@) (Mul d0~8@ c0~6@)) (Mul (Mul d0~8@ d0~8@) (Mul d0~8@ a0~2@)))
     )))
     (=>
      (= temp_0_1~434@ (Mul (Mul (Mul (Mul (Mul a0~2@ b0~4@) (Mul d0~8@ c0~6@)) (Mul (Mul d0~8@
            c0~6@
           ) (Mul d0~8@ c0~6@)
          )
         ) (Mul (Mul (Mul b0~4@ d0~8@) (Mul b0~4@ c0~6@)) (Mul (Mul c0~6@ 84) c0~6@))
        ) (Mul (Mul (Add (Mul a0~2@ d0~8@) (Mul d0~8@ c0~6@)) (Mul (Mul b0~4@ a0~2@) (Mul c0~6@
            b0~4@
          ))
         ) (Mul (Mul (Mul c0~6@ c0~6@) (Mul d0~8@ c0~6@)) (Mul (Mul d0~8@ d0~8@) (Mul d0~8@ a0~2@)))
      )))
      (and
       (=>
        (ens%main!nl_basics.lemma_mul_is_commutative. c0~6@ b0~4@)
        (=>
         %%location_label%%0
         (= temp_0_0~297@ temp_0_1~434@)
       ))
       (=>
        (= temp_0_0~297@ temp_0_1~434@)
        (=>
         (= temp_1_0~571@ (Mul (Mul (Mul (Mul (Mul a1~10@ a1~10@) c1~14@) c1~14@) (Mul (Mul (Mul
               d1~16@ c1~14@
              ) (Mul b1~12@ a1~10@)
             ) (Mul (Mul b1~12@ b1~12@) (Mul c1~14@ b1~12@))
            )
           ) (Mul (Mul (Mul (Mul d1~16@ a1~10@) d1~16@) (Mul (Mul b1~12@ d1~16@) (Mul c1~14@ d1~16@)))
            (Mul (Mul (Mul b1~12@ d1~16@) (Mul c1~14@ c1~14@)) (Mul (Mul b1~12@ b1~12@) (Mul d1~16@
               a1~10@
         ))))))
         (=>
          (= temp_1_1~680@ (Mul (Mul (Mul (Mul a1~10@ a1~10@) c1~14@) (Mul c1~14@ (Mul (Mul (Mul d1~16@
                 c1~14@
                ) (Mul b1~12@ a1~10@)
               ) (Mul (Mul b1~12@ b1~12@) (Mul c1~14@ b1~12@))
             ))
            ) (Mul (Mul (Mul (Mul d1~16@ a1~10@) d1~16@) (Mul (Mul b1~12@ d1~16@) (Mul c1~14@ d1~16@)))
             (Mul (Mul (Mul b1~12@ d1~16@) (Mul c1~14@ c1~14@)) (Mul (Mul b1~12@ b1~12@) (Mul d1~16@
                a1~10@
          ))))))
          (and
           (=>
            (= tmp%1@ (Mul (Mul a1~10@ a1~10@) c1~14@))
            (=>
             (= tmp%2@ (Mul (Mul (Mul d1~16@ c1~14@) (Mul b1~12@ a1~10@)) (Mul (Mul b1~12@ b1~12@)
                (Mul c1~14@ b1~12@)
             )))
             (=>
              (ens%main!nl_basics.lemma_mul_is_associative. tmp%1@ c1~14@ tmp%2@)
              (=>
               %%location_label%%1
               (= temp_1_0~571@ temp_1_1~680@)
           ))))
           (=>
            (= temp_1_0~571@ temp_1_1~680@)
            (=>
             (= temp_2_0~855@ (Mul (Mul (Mul (Mul (Add c2~22@ a2~18@) (Mul a2~18@ c2~22@)) (Mul b2~20@
                  d2~24@
                 )
                ) (Mul (Mul (Add a2~18@ d2~24@) (Mul d2~24@ d2~24@)) (Add (Mul b2~20@ c2~22@) (Sub a2~18@
                   b2~20@
                )))
               ) (Mul (Mul (Mul (Mul d2~24@ a2~18@) (Mul d2~24@ b2~20@)) (Mul (Mul b2~20@ d2~24@) (
                   Mul c2~22@ a2~18@
                 ))
                ) (Mul d2~24@ (Mul (Mul c2~22@ d2~24@) (Mul a2~18@ c2~22@)))
             )))
             (=>
              (= temp_2_1~964@ (Mul (Mul (Mul (Mul (Add c2~22@ a2~18@) (Mul a2~18@ c2~22@)) (Mul b2~20@
                   d2~24@
                  )
                 ) (Mul (Mul (Add a2~18@ d2~24@) (Mul d2~24@ d2~24@)) (Add (Mul b2~20@ c2~22@) (Sub a2~18@
                    b2~20@
                 )))
                ) (Mul (Mul (Mul (Mul d2~24@ a2~18@) (Mul d2~24@ b2~20@)) (Mul (Mul b2~20@ d2~24@) (
                    Mul c2~22@ a2~18@
                  ))
                 ) (Mul d2~24@ (Mul (Mul d2~24@ c2~22@) (Mul a2~18@ c2~22@)))
              )))
              (and
               (=>
                (ens%main!nl_basics.lemma_mul_is_commutative. c2~22@ d2~24@)
                (=>
                 %%location_label%%2
                 (= temp_2_0~855@ temp_2_1~964@)
               ))
               (=>
                (= temp_2_0~855@ temp_2_1~964@)
                (=>
                 (= temp_3_0~1121@ (Mul (Mul (Add (Mul (Mul b3~28@ b3~28@) (Mul a3~26@ c3~30@)) (Mul (Mul
                       a3~26@ c3~30@
                      ) (Mul b3~28@ d3~32@)
                     )
                    ) (Mul (Sub (Mul c3~30@ b3~28@) (Mul d3~32@ b3~28@)) (Add (Mul c3~30@ c3~30@) (Mul d3~32@
                       a3~26@
                    )))
                   ) (Sub (Mul (Mul (Mul c3~30@ d3~32@) (Mul a3~26@ a3~26@)) (Mul (Mul a3~26@ b3~28@) (
                       Mul a3~26@ d3~32@
                     ))
                    ) (Mul (Mul (Mul c3~30@ d3~32@) (Mul b3~28@ d3~32@)) (Mul (Mul d3~32@ a3~26@) (Mul c3~30@
                       c3~30@
                 ))))))
                 (=>
                  (= temp_3_1~1250@ (Mul (Mul (Add (Mul (Mul b3~28@ b3~28@) (Mul a3~26@ c3~30@)) (Mul (Mul
                        a3~26@ c3~30@
                       ) (Mul b3~28@ d3~32@)
                      )
                     ) (Mul (Sub (Mul c3~30@ b3~28@) (Mul d3~32@ b3~28@)) (Add (Mul c3~30@ c3~30@) (Mul d3~32@
                        a3~26@
                     )))
                    ) (Sub (Mul (Mul (Mul c3~30@ d3~32@) (Mul a3~26@ a3~26@)) (Mul (Mul a3~26@ b3~28@) (
                        Mul a3~26@ d3~32@
                      ))
                     ) (Mul (Mul (Mul d3~32@ c3~30@) (Mul b3~28@ d3~32@)) (Mul (Mul d3~32@ a3~26@) (Mul c3~30@
                        c3~30@
                  ))))))
                  (and
                   (=>
                    (ens%main!nl_basics.lemma_mul_is_commutative. c3~30@ d3~32@)
                    (=>
                     %%location_label%%3
                     (= temp_3_0~1121@ temp_3_1~1250@)
                   ))
                   (=>
                    (= temp_3_0~1121@ temp_3_1~1250@)
                    (=>
                     (= temp_4_0~1367@ (Mul (Mul (Mul (Mul (Mul a4~34@ c4~38@) (Mul b4~36@ c4~38@)) (Mul (Sub
                           d4~40@ b4~36@
                          ) (Mul b4~36@ c4~38@)
                         )
                        ) b4~36@
                       ) (Add (Mul (Mul (Mul b4~36@ c4~38@) d4~40@) (Mul (Mul a4~34@ a4~34@) a4~34@)) (Mul
                         (Mul b4~36@ (Mul a4~34@ b4~36@)) (Sub (Mul c4~38@ d4~40@) (Sub b4~36@ b4~36@))
                     ))))
                     (=>
                      (= temp_4_1~1456@ (Mul (Mul (Mul (Mul (Mul a4~34@ c4~38@) (Mul b4~36@ c4~38@)) (Mul (Sub
                            d4~40@ b4~36@
                           ) (Mul b4~36@ c4~38@)
                          )
                         ) b4~36@
                        ) (Add (Mul (Mul (Mul c4~38@ b4~36@) d4~40@) (Mul (Mul a4~34@ a4~34@) a4~34@)) (Mul
                          (Mul b4~36@ (Mul a4~34@ b4~36@)) (Sub (Mul c4~38@ d4~40@) (Sub b4~36@ b4~36@))
                      ))))
                      (and
                       (=>
                        (ens%main!nl_basics.lemma_mul_is_commutative. b4~36@ c4~38@)
                        (=>
                         %%location_label%%4
                         (= temp_4_0~1367@ temp_4_1~1456@)
                       ))
                       (=>
                        (= temp_4_0~1367@ temp_4_1~1456@)
                        (=>
                         (= temp_5_0~1637@ (Mul (Add (Mul (Mul (Mul d5~48@ d5~48@) (Mul a5~42@ b5~44@)) (Mul (Mul
                               a5~42@ b5~44@
                              ) (Mul a5~42@ a5~42@)
                             )
                            ) (Mul (Mul (Mul d5~48@ b5~44@) (Mul c5~46@ b5~44@)) (Mul (Mul c5~46@ b5~44@) (Mul b5~44@
                               c5~46@
                            )))
                           ) (Mul (Mul (Mul (Mul a5~42@ d5~48@) (Mul c5~46@ a5~42@)) (Mul (Mul b5~44@ a5~42@) (
                               Sub b5~44@ 13
                             ))
                            ) (Mul (Add (Mul d5~48@ 64) (Mul d5~48@ c5~46@)) (Mul (Mul d5~48@ a5~42@) (Mul a5~42@
                               b5~44@
                         ))))))
                         (=>
                          (= temp_5_1~1790@ (Mul (Mul (Mul (Mul (Mul a5~42@ d5~48@) (Mul c5~46@ a5~42@)) (Mul (Mul
                                b5~44@ a5~42@
                               ) (Sub b5~44@ 13)
                              )
                             ) (Mul (Add (Mul d5~48@ 64) (Mul d5~48@ c5~46@)) (Mul (Mul d5~48@ a5~42@) (Mul a5~42@
                                b5~44@
                             )))
                            ) (Add (Mul (Mul (Mul d5~48@ d5~48@) (Mul a5~42@ b5~44@)) (Mul (Mul a5~42@ b5~44@) (
                                Mul a5~42@ a5~42@
                              ))
                             ) (Mul (Mul (Mul d5~48@ b5~44@) (Mul c5~46@ b5~44@)) (Mul (Mul c5~46@ b5~44@) (Mul b5~44@
                                c5~46@
                          ))))))
                          (and
                           (=>
                            (= tmp%3@ (Add (Mul (Mul (Mul d5~48@ d5~48@) (Mul a5~42@ b5~44@)) (Mul (Mul a5~42@ b5~44@)
                                (Mul a5~42@ a5~42@)
                               )
                              ) (Mul (Mul (Mul d5~48@ b5~44@) (Mul c5~46@ b5~44@)) (Mul (Mul c5~46@ b5~44@) (Mul b5~44@
                                 c5~46@
                            )))))
                            (=>
                             (= tmp%4@ (Mul (Mul (Mul (Mul a5~42@ d5~48@) (Mul c5~46@ a5~42@)) (Mul (Mul b5~44@ a5~42@)
                                 (Sub b5~44@ 13)
                                )
                               ) (Mul (Add (Mul d5~48@ 64) (Mul d5~48@ c5~46@)) (Mul (Mul d5~48@ a5~42@) (Mul a5~42@
                                  b5~44@
                             )))))
                             (=>
                              (ens%main!nl_basics.lemma_mul_is_commutative. tmp%3@ tmp%4@)
                              (=>
                               %%location_label%%5
                               (= temp_5_0~1637@ temp_5_1~1790@)
                           ))))
                           (=>
                            (= temp_5_0~1637@ temp_5_1~1790@)
                            (=>
                             (= temp_6_0~2063@ (Mul (Mul b6~52@ (Mul (Add (Mul d6~56@ a6~50@) (Mul c6~54@ c6~54@))
                                 (Mul (Mul a6~50@ a6~50@) d6~56@)
                                )
                               ) (Mul (Mul (Mul (Mul b6~52@ c6~54@) (Mul c6~54@ d6~56@)) (Mul (Mul d6~56@ a6~50@) (
                                   Mul 35 d6~56@
                                 ))
                                ) (Mul (Mul (Add b6~52@ a6~50@) a6~50@) (Mul (Mul c6~54@ c6~54@) d6~56@))
                             )))
                             (=>
                              (= temp_6_1~2164@ (Mul (Mul b6~52@ (Mul (Add (Mul d6~56@ a6~50@) (Mul c6~54@ c6~54@))
                                  (Mul (Mul a6~50@ a6~50@) d6~56@)
                                 )
                                ) (Mul (Mul (Mul (Mul b6~52@ c6~54@) (Mul c6~54@ d6~56@)) (Mul (Mul d6~56@ a6~50@) (
                                    Mul d6~56@ 35
                                  ))
                                 ) (Mul (Mul (Add b6~52@ a6~50@) a6~50@) (Mul (Mul c6~54@ c6~54@) d6~56@))
                              )))
                              (and
                               (=>
                                (ens%main!nl_basics.lemma_mul_is_commutative. 35 d6~56@)
                                (=>
                                 %%location_label%%6
                                 (= temp_6_0~2063@ temp_6_1~2164@)
                               ))
                               (=>
                                (= temp_6_0~2063@ temp_6_1~2164@)
                                (=>
                                 (= temp_7_0~2313@ (Mul (Mul (Mul (Mul a7~58@ (Mul c7~62@ 20)) d7~64@) (Sub (Mul (Mul d7~64@
                                       a7~58@
                                      ) (Sub b7~60@ c7~62@)
                                     ) (Mul (Mul d7~64@ a7~58@) (Sub a7~58@ c7~62@))
                                    )
                                   ) (Mul (Mul b7~60@ (Mul c7~62@ (Mul d7~64@ c7~62@))) (Mul (Mul (Sub c7~62@ b7~60@) (
                                       Mul c7~62@ d7~64@
                                      )
                                     ) (Mul (Mul a7~58@ b7~60@) (Mul d7~64@ d7~64@))
                                 ))))
                                 (=>
                                  (= temp_7_1~2422@ (Mul (Mul (Mul (Mul (Mul c7~62@ 20) a7~58@) d7~64@) (Sub (Mul (Mul d7~64@
                                        a7~58@
                                       ) (Sub b7~60@ c7~62@)
                                      ) (Mul (Mul d7~64@ a7~58@) (Sub a7~58@ c7~62@))
                                     )
                                    ) (Mul (Mul b7~60@ (Mul c7~62@ (Mul d7~64@ c7~62@))) (Mul (Mul (Sub c7~62@ b7~60@) (
                                        Mul c7~62@ d7~64@
                                       )
                                      ) (Mul (Mul a7~58@ b7~60@) (Mul d7~64@ d7~64@))
                                  ))))
                                  (and
                                   (=>
                                    (= tmp%5@ (Mul c7~62@ 20))
                                    (=>
                                     (ens%main!nl_basics.lemma_mul_is_commutative. a7~58@ tmp%5@)
                                     (=>
                                      %%location_label%%7
                                      (= temp_7_0~2313@ temp_7_1~2422@)
                                   )))
                                   (=>
                                    (= temp_7_0~2313@ temp_7_1~2422@)
                                    (=>
                                     (= temp_8_0~2599@ (Mul (Mul (Mul (Mul (Mul c8~70@ 43) (Sub b8~68@ d8~72@)) (Add (Mul d8~72@
                                           b8~68@
                                          ) (Mul b8~68@ c8~70@)
                                         )
                                        ) (Mul (Add (Mul a8~66@ c8~70@) b8~68@) (Mul (Mul d8~72@ d8~72@) (Mul c8~70@ d8~72@)))
                                       ) (Mul (Mul (Mul (Mul b8~68@ d8~72@) (Mul c8~70@ c8~70@)) (Mul (Mul a8~66@ c8~70@) (
                                           Mul a8~66@ c8~70@
                                         ))
                                        ) (Mul (Mul (Sub d8~72@ a8~66@) (Add d8~72@ a8~66@)) (Mul (Mul a8~66@ d8~72@) c8~70@))
                                     )))
                                     (=>
                                      (= temp_8_1~2732@ (Mul (Mul (Mul (Mul (Mul c8~70@ 43) (Sub b8~68@ d8~72@)) (Add (Mul d8~72@
                                            b8~68@
                                           ) (Mul b8~68@ c8~70@)
                                          )
                                         ) (Mul (Add (Mul a8~66@ c8~70@) b8~68@) (Mul (Mul d8~72@ d8~72@) (Mul c8~70@ d8~72@)))
                                        ) (Mul (Mul (Mul (Mul b8~68@ d8~72@) (Mul c8~70@ c8~70@)) (Mul (Mul a8~66@ c8~70@) (
                                            Mul c8~70@ a8~66@
                                          ))
                                         ) (Mul (Mul (Sub d8~72@ a8~66@) (Add d8~72@ a8~66@)) (Mul (Mul a8~66@ d8~72@) c8~70@))
                                      )))
                                      (and
                                       (=>
                                        (ens%main!nl_basics.lemma_mul_is_commutative. a8~66@ c8~70@)
                                        (=>
                                         %%location_label%%8
                                         (= temp_8_0~2599@ temp_8_1~2732@)
                                       ))
                                       (=>
                                        (= temp_8_0~2599@ temp_8_1~2732@)
                                        (=>
                                         (= temp_9_0~2821@ (Mul (Mul (Mul (Sub b9~76@ (Mul a9~74@ b9~76@)) (Sub (Mul c9~78@ a9~74@)
                                              d9~80@
                                             )
                                            ) a9~74@
                                           ) (Mul (Mul (Mul (Mul b9~76@ a9~74@) a9~74@) (Sub (Mul d9~80@ d9~80@) (Sub a9~74@ a9~74@)))
                                            d9~80@
                                         )))
                                         (=>
                                          (= temp_9_1~2882@ (Mul (Mul (Mul (Sub b9~76@ (Mul a9~74@ b9~76@)) (Sub (Mul c9~78@ a9~74@)
                                               d9~80@
                                              )
                                             ) a9~74@
                                            ) (Mul (Mul (Mul b9~76@ a9~74@) (Mul a9~74@ (Sub (Mul d9~80@ d9~80@) (Sub a9~74@ a9~74@))))
                                             d9~80@
                                          )))
                                          (and
                                           (=>
                                            (= tmp%6@ (Mul b9~76@ a9~74@))
                                            (=>
                                             (= tmp%7@ (Sub (Mul d9~80@ d9~80@) (Sub a9~74@ a9~74@)))
                                             (=>
                                              (ens%main!nl_basics.lemma_mul_is_associative. tmp%6@ a9~74@ tmp%7@)
                                              (=>
                                               %%location_label%%9
                                               (= temp_9_0~2821@ temp_9_1~2882@)
                                           ))))
                                           (=>
                                            (= temp_9_0~2821@ temp_9_1~2882@)
                                            (=>
                                             (= temp_10_0~3001@ (Mul (Mul (Mul (Mul (Sub a10~82@ a10~82@) (Mul d10~88@ b10~84@)) (
                                                  Mul (Mul c10~86@ a10~82@) (Sub a10~82@ c10~86@)
                                                 )
                                                ) d10~88@
                                               ) (Mul d10~88@ (Mul (Mul (Mul d10~88@ d10~88@) (Sub c10~86@ b10~84@)) (Mul (Mul d10~88@
                                                   b10~84@
                                                  ) (Add c10~86@ c10~86@)
                                             )))))
                                             (=>
                                              (= temp_10_1~3074@ (Mul (Mul (Mul (Mul (Sub a10~82@ a10~82@) (Mul d10~88@ b10~84@)) (
                                                   Mul (Mul c10~86@ a10~82@) (Sub a10~82@ c10~86@)
                                                  )
                                                 ) d10~88@
                                                ) (Mul d10~88@ (Mul (Mul (Mul d10~88@ b10~84@) (Add c10~86@ c10~86@)) (Mul (Mul d10~88@
                                                    d10~88@
                                                   ) (Sub c10~86@ b10~84@)
                                              )))))
                                              (and
                                               (=>
                                                (= tmp%8@ (Mul (Mul d10~88@ d10~88@) (Sub c10~86@ b10~84@)))
                                                (=>
                                                 (= tmp%9@ (Mul (Mul d10~88@ b10~84@) (Add c10~86@ c10~86@)))
                                                 (=>
                                                  (ens%main!nl_basics.lemma_mul_is_commutative. tmp%8@ tmp%9@)
                                                  (=>
                                                   %%location_label%%10
                                                   (= temp_10_0~3001@ temp_10_1~3074@)
                                               ))))
                                               (=>
                                                (= temp_10_0~3001@ temp_10_1~3074@)
                                                (=>
                                                 (= temp_11_0~3187@ (Mul (Mul (Mul b11~92@ (Mul (Sub a11~90@ d11~96@) (Mul c11~94@ b11~92@)))
                                                    c11~94@
                                                   ) (Mul c11~94@ (Mul (Mul (Add a11~90@ d11~96@) (Mul a11~90@ a11~90@)) (Sub (Mul d11~96@
                                                       a11~90@
                                                      ) (Mul b11~92@ c11~94@)
                                                 )))))
                                                 (=>
                                                  (= temp_11_1~3248@ (Mul (Mul c11~94@ (Mul b11~92@ (Mul (Sub a11~90@ d11~96@) (Mul c11~94@
                                                        b11~92@
                                                     )))
                                                    ) (Mul c11~94@ (Mul (Mul (Add a11~90@ d11~96@) (Mul a11~90@ a11~90@)) (Sub (Mul d11~96@
                                                        a11~90@
                                                       ) (Mul b11~92@ c11~94@)
                                                  )))))
                                                  (and
                                                   (=>
                                                    (= tmp%10@ (Mul b11~92@ (Mul (Sub a11~90@ d11~96@) (Mul c11~94@ b11~92@))))
                                                    (=>
                                                     (ens%main!nl_basics.lemma_mul_is_commutative. tmp%10@ c11~94@)
                                                     (=>
                                                      %%location_label%%11
                                                      (= temp_11_0~3187@ temp_11_1~3248@)
                                                   )))
                                                   (=>
                                                    (= temp_11_0~3187@ temp_11_1~3248@)
                                                    (=>
                                                     (= temp_12_0~3413@ (Add (Mul (Add (Add (Mul b12~100@ d12~104@) (Mul d12~104@ b12~100@))
                                                         (Mul (Mul a12~98@ a12~98@) (Mul a12~98@ b12~100@))
                                                        ) (Add (Mul (Mul d12~104@ c12~102@) b12~100@) a12~98@)
                                                       ) (Mul (Sub (Add (Mul c12~102@ a12~98@) (Mul c12~102@ d12~104@)) (Mul (Mul a12~98@ b12~100@)
                                                          c12~102@
                                                         )
                                                        ) (Mul (Mul (Mul d12~104@ d12~104@) (Mul a12~98@ c12~102@)) (Mul (Mul 69 a12~98@) (
                                                           Mul c12~102@ c12~102@
                                                     ))))))
                                                     (=>
                                                      (= temp_12_1~3566@ (Add (Add (Mul (Add (Add (Mul b12~100@ d12~104@) (Mul d12~104@ b12~100@))
                                                           (Mul (Mul a12~98@ a12~98@) (Mul a12~98@ b12~100@))
                                                          ) (Mul (Mul d12~104@ c12~102@) b12~100@)
                                                         ) (Mul (Add (Add (Mul b12~100@ d12~104@) (Mul d12~104@ b12~100@)) (Mul (Mul a12~98@ a12~98@)
                                                            (Mul a12~98@ b12~100@)
                                                           )
                                                          ) a12~98@
                                                         )
                                                        ) (Mul (Sub (Add (Mul c12~102@ a12~98@) (Mul c12~102@ d12~104@)) (Mul (Mul a12~98@ b12~100@)
                                                           c12~102@
                                                          )
                                                         ) (Mul (Mul (Mul d12~104@ d12~104@) (Mul a12~98@ c12~102@)) (Mul (Mul 69 a12~98@) (
                                                            Mul c12~102@ c12~102@
                                                      ))))))
                                                      (and
                                                       (=>
                                                        (= tmp%11@ (Add (Add (Mul b12~100@ d12~104@) (Mul d12~104@ b12~100@)) (Mul (Mul a12~98@
                                                            a12~98@
                                                           ) (Mul a12~98@ b12~100@)
                                                        )))
                                                        (=>
                                                         (= tmp%12@ (Mul (Mul d12~104@ c12~102@) b12~100@))
                                                         (=>
                                                          (ens%main!nl_basics.lemma_mul_is_distributive. tmp%11@ tmp%12@ a12~98@)
                                                          (=>
                                                           %%location_label%%12
                                                           (= temp_12_0~3413@ temp_12_1~3566@)
                                                       ))))
                                                       (=>
                                                        (= temp_12_0~3413@ temp_12_1~3566@)
                                                        (=>
                                                         (= temp_13_0~3765@ (Mul (Mul (Sub (Mul (Mul b13~108@ c13~110@) a13~106@) (Mul (Mul a13~106@
                                                               d13~112@
                                                              ) (Mul b13~108@ a13~106@)
                                                             )
                                                            ) (Mul (Mul (Mul 51 d13~112@) a13~106@) (Mul (Mul b13~108@ c13~110@) (Mul b13~108@ a13~106@)))
                                                           ) (Mul (Mul b13~108@ (Sub (Add b13~108@ d13~112@) (Mul a13~106@ d13~112@))) (Mul (Mul
                                                              (Mul a13~106@ a13~106@) (Mul b13~108@ d13~112@)
                                                             ) (Mul (Mul 48 a13~106@) (Mul c13~110@ d13~112@))
                                                         ))))
                                                         (=>
                                                          (= temp_13_1~3938@ (Mul (Sub (Mul (Mul (Mul b13~108@ c13~110@) a13~106@) (Mul (Mul (Mul
                                                                 51 d13~112@
                                                                ) a13~106@
                                                               ) (Mul (Mul b13~108@ c13~110@) (Mul b13~108@ a13~106@))
                                                              )
                                                             ) (Mul (Mul (Mul a13~106@ d13~112@) (Mul b13~108@ a13~106@)) (Mul (Mul (Mul 51 d13~112@)
                                                                a13~106@
                                                               ) (Mul (Mul b13~108@ c13~110@) (Mul b13~108@ a13~106@))
                                                             ))
                                                            ) (Mul (Mul b13~108@ (Sub (Add b13~108@ d13~112@) (Mul a13~106@ d13~112@))) (Mul (Mul
                                                               (Mul a13~106@ a13~106@) (Mul b13~108@ d13~112@)
                                                              ) (Mul (Mul 48 a13~106@) (Mul c13~110@ d13~112@))
                                                          ))))
                                                          (and
                                                           (=>
                                                            (= tmp%13@ (Mul (Mul b13~108@ c13~110@) a13~106@))
                                                            (=>
                                                             (= tmp%14@ (Mul (Mul a13~106@ d13~112@) (Mul b13~108@ a13~106@)))
                                                             (=>
                                                              (= tmp%15@ (Mul (Mul (Mul 51 d13~112@) a13~106@) (Mul (Mul b13~108@ c13~110@) (Mul b13~108@
                                                                  a13~106@
                                                              ))))
                                                              (=>
                                                               (ens%main!nl_basics.lemma_mul_is_distributive. tmp%13@ tmp%14@ tmp%15@)
                                                               (=>
                                                                %%location_label%%13
                                                                (= temp_13_0~3765@ temp_13_1~3938@)
                                                           )))))
                                                           (=>
                                                            (= temp_13_0~3765@ temp_13_1~3938@)
                                                            (=>
                                                             (= temp_14_0~4149@ (Mul (Mul (Sub (Mul (Sub c14~118@ b14~116@) d14~120@) (Mul (Add a14~114@
                                                                   a14~114@
                                                                  ) (Mul b14~116@ b14~116@)
                                                                 )
                                                                ) (Mul (Add (Mul d14~120@ b14~116@) (Mul d14~120@ a14~114@)) (Mul (Mul a14~114@ 47)
                                                                  (Mul a14~114@ d14~120@)
                                                                ))
                                                               ) (Mul (Mul 97 (Mul (Mul b14~116@ d14~120@) a14~114@)) (Mul (Mul (Mul b14~116@ d14~120@)
                                                                  d14~120@
                                                                 ) (Mul (Mul d14~120@ a14~114@) a14~114@)
                                                             ))))
                                                             (=>
                                                              (= temp_14_1~4274@ (Mul (Mul (Sub (Mul (Sub c14~118@ b14~116@) d14~120@) (Mul (Add a14~114@
                                                                    a14~114@
                                                                   ) (Mul b14~116@ b14~116@)
                                                                  )
                                                                 ) (Mul (Add (Mul d14~120@ b14~116@) (Mul a14~114@ d14~120@)) (Mul (Mul a14~114@ 47)
                                                                   (Mul a14~114@ d14~120@)
                                                                 ))
                                                                ) (Mul (Mul 97 (Mul (Mul b14~116@ d14~120@) a14~114@)) (Mul (Mul (Mul b14~116@ d14~120@)
                                                                   d14~120@
                                                                  ) (Mul (Mul d14~120@ a14~114@) a14~114@)
                                                              ))))
                                                              (=>
                                                               (ens%main!nl_basics.lemma_mul_is_commutative. d14~120@ a14~114@)
                                                               (=>
                                                                %%location_label%%14
                                                                (= temp_14_0~4149@ temp_14_1~4274@)
 )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
 (get-info :version)
 (assert
  %%query%%
 )
 (set-option :rlimit 4294967295)
 (check-sat)
 (set-option :rlimit 0)
(pop)
