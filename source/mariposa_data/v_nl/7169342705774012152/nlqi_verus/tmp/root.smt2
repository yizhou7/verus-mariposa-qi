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
;; mariposa_data/v_nl//7169342705774012152/nlqi_verus/src/main.rs:7:1: 26:40 (#0)
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
 (declare-const temp_0_0~301@ Int)
 (declare-const temp_0_1~450@ Int)
 (declare-const temp_1_0~629@ Int)
 (declare-const temp_1_1~762@ Int)
 (declare-const temp_2_0~877@ Int)
 (declare-const temp_2_1~958@ Int)
 (declare-const temp_3_0~1207@ Int)
 (declare-const temp_3_1~1356@ Int)
 (declare-const temp_4_0~1513@ Int)
 (declare-const temp_4_1~1630@ Int)
 (declare-const temp_5_0~1783@ Int)
 (declare-const temp_5_1~1884@ Int)
 (declare-const temp_6_0~1997@ Int)
 (declare-const temp_6_1~2082@ Int)
 (declare-const temp_7_0~2297@ Int)
 (declare-const temp_7_1~2410@ Int)
 (declare-const temp_8_0~2547@ Int)
 (declare-const temp_8_1~2632@ Int)
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
 (declare-const %%query%% Bool)
 (assert
  (=>
   %%query%%
   (not (=>
     (= temp_0_0~301@ (Add (Mul (Mul (Mul (Sub d0~8@ a0~2@) (Mul b0~4@ d0~8@)) (Add (Mul c0~6@
           d0~8@
          ) (Mul a0~2@ c0~6@)
         )
        ) (Mul (Mul (Mul d0~8@ a0~2@) (Add a0~2@ c0~6@)) (Mul (Mul c0~6@ c0~6@) (Add a0~2@ c0~6@)))
       ) (Mul (Mul (Mul (Mul b0~4@ d0~8@) (Mul c0~6@ b0~4@)) (Mul (Mul b0~4@ a0~2@) (Add d0~8@
           d0~8@
         ))
        ) (Add (Mul (Mul c0~6@ d0~8@) (Mul d0~8@ a0~2@)) (Mul (Sub d0~8@ 63) (Sub a0~2@ c0~6@)))
     )))
     (=>
      (= temp_0_1~450@ (Add (Mul (Mul (Mul (Sub d0~8@ a0~2@) (Mul b0~4@ d0~8@)) (Add (Mul c0~6@
            d0~8@
           ) (Mul a0~2@ c0~6@)
          )
         ) (Mul (Mul (Mul d0~8@ a0~2@) (Add a0~2@ c0~6@)) (Mul (Mul c0~6@ c0~6@) (Add a0~2@ c0~6@)))
        ) (Mul (Mul (Mul (Mul b0~4@ d0~8@) (Mul c0~6@ b0~4@)) (Mul (Mul b0~4@ a0~2@) (Add d0~8@
            d0~8@
          ))
         ) (Add (Mul (Mul c0~6@ d0~8@) (Mul d0~8@ a0~2@)) (Sub (Mul d0~8@ (Sub a0~2@ c0~6@))
           (Mul 63 (Sub a0~2@ c0~6@))
      )))))
      (and
       (=>
        (= tmp%1@ (Sub a0~2@ c0~6@))
        (=>
         (ens%main!nl_basics.lemma_mul_is_distributive. d0~8@ 63 tmp%1@)
         (=>
          %%location_label%%0
          (= temp_0_0~301@ temp_0_1~450@)
       )))
       (=>
        (= temp_0_0~301@ temp_0_1~450@)
        (=>
         (= temp_1_0~629@ (Mul (Mul (Mul (Mul (Mul c1~14@ a1~10@) (Mul a1~10@ d1~16@)) (Add (Mul
               a1~10@ c1~14@
              ) b1~12@
             )
            ) (Mul (Add (Mul b1~12@ a1~10@) (Mul b1~12@ b1~12@)) (Mul (Mul b1~12@ b1~12@) (Mul b1~12@
               a1~10@
            )))
           ) (Mul (Mul (Mul (Add a1~10@ b1~12@) d1~16@) (Mul (Mul c1~14@ 8) (Sub d1~16@ d1~16@)))
            (Mul (Mul (Sub a1~10@ a1~10@) (Mul b1~12@ b1~12@)) (Sub (Mul c1~14@ c1~14@) (Sub a1~10@
               c1~14@
         ))))))
         (=>
          (= temp_1_1~762@ (Mul (Mul (Mul (Mul (Mul c1~14@ a1~10@) (Mul a1~10@ d1~16@)) (Add (Mul
                a1~10@ c1~14@
               ) b1~12@
              )
             ) (Mul (Add (Mul b1~12@ a1~10@) (Mul b1~12@ b1~12@)) (Mul (Mul (Mul b1~12@ b1~12@) b1~12@)
               a1~10@
             ))
            ) (Mul (Mul (Mul (Add a1~10@ b1~12@) d1~16@) (Mul (Mul c1~14@ 8) (Sub d1~16@ d1~16@)))
             (Mul (Mul (Sub a1~10@ a1~10@) (Mul b1~12@ b1~12@)) (Sub (Mul c1~14@ c1~14@) (Sub a1~10@
                c1~14@
          ))))))
          (and
           (=>
            (= tmp%2@ (Mul b1~12@ b1~12@))
            (=>
             (ens%main!nl_basics.lemma_mul_is_associative. tmp%2@ b1~12@ a1~10@)
             (=>
              %%location_label%%1
              (= temp_1_0~629@ temp_1_1~762@)
           )))
           (=>
            (= temp_1_0~629@ temp_1_1~762@)
            (=>
             (= temp_2_0~877@ (Mul a2~18@ (Mul (Mul (Mul (Mul d2~24@ b2~20@) (Mul d2~24@ 87)) (Sub
                  (Mul a2~18@ a2~18@) (Mul c2~22@ d2~24@)
                 )
                ) (Sub (Sub (Mul c2~22@ c2~22@) (Mul a2~18@ b2~20@)) (Add (Mul a2~18@ c2~22@) (Sub a2~18@
                   a2~18@
             ))))))
             (=>
              (= temp_2_1~958@ (Mul (Mul (Mul (Mul (Mul d2~24@ b2~20@) (Mul d2~24@ 87)) (Sub (Mul a2~18@
                    a2~18@
                   ) (Mul c2~22@ d2~24@)
                  )
                 ) (Sub (Sub (Mul c2~22@ c2~22@) (Mul a2~18@ b2~20@)) (Add (Mul a2~18@ c2~22@) (Sub a2~18@
                    a2~18@
                 )))
                ) a2~18@
              ))
              (and
               (=>
                (= tmp%3@ (Mul (Mul (Mul (Mul d2~24@ b2~20@) (Mul d2~24@ 87)) (Sub (Mul a2~18@ a2~18@)
                    (Mul c2~22@ d2~24@)
                   )
                  ) (Sub (Sub (Mul c2~22@ c2~22@) (Mul a2~18@ b2~20@)) (Add (Mul a2~18@ c2~22@) (Sub a2~18@
                     a2~18@
                )))))
                (=>
                 (ens%main!nl_basics.lemma_mul_is_commutative. a2~18@ tmp%3@)
                 (=>
                  %%location_label%%2
                  (= temp_2_0~877@ temp_2_1~958@)
               )))
               (=>
                (= temp_2_0~877@ temp_2_1~958@)
                (=>
                 (= temp_3_0~1207@ (Mul (Add (Sub (Mul (Mul c3~30@ c3~30@) (Mul a3~26@ a3~26@)) (Mul (Mul
                       a3~26@ b3~28@
                      ) (Add b3~28@ c3~30@)
                     )
                    ) (Mul (Add (Mul a3~26@ b3~28@) (Mul a3~26@ d3~32@)) (Mul (Mul b3~28@ c3~30@) c3~30@))
                   ) (Mul (Mul (Mul (Mul a3~26@ 15) (Mul a3~26@ d3~32@)) (Mul (Mul a3~26@ d3~32@) (Mul d3~32@
                       d3~32@
                     ))
                    ) (Mul (Mul (Sub a3~26@ b3~28@) (Mul a3~26@ d3~32@)) (Mul (Mul 1 b3~28@) (Mul a3~26@
                       d3~32@
                 ))))))
                 (=>
                  (= temp_3_1~1356@ (Mul (Add (Sub (Mul (Mul c3~30@ c3~30@) (Mul a3~26@ a3~26@)) (Mul (Mul
                        a3~26@ b3~28@
                       ) (Add b3~28@ c3~30@)
                      )
                     ) (Mul (Add (Mul a3~26@ b3~28@) (Mul a3~26@ d3~32@)) (Mul (Mul b3~28@ c3~30@) c3~30@))
                    ) (Mul (Mul (Mul (Mul 15 a3~26@) (Mul a3~26@ d3~32@)) (Mul (Mul a3~26@ d3~32@) (Mul d3~32@
                        d3~32@
                      ))
                     ) (Mul (Mul (Sub a3~26@ b3~28@) (Mul a3~26@ d3~32@)) (Mul (Mul 1 b3~28@) (Mul a3~26@
                        d3~32@
                  ))))))
                  (and
                   (=>
                    (ens%main!nl_basics.lemma_mul_is_commutative. a3~26@ 15)
                    (=>
                     %%location_label%%3
                     (= temp_3_0~1207@ temp_3_1~1356@)
                   ))
                   (=>
                    (= temp_3_0~1207@ temp_3_1~1356@)
                    (=>
                     (= temp_4_0~1513@ (Mul (Mul (Mul (Mul (Mul b4~36@ d4~40@) (Mul a4~34@ a4~34@)) (Mul (Mul
                           d4~40@ c4~38@
                          ) (Mul b4~36@ d4~40@)
                         )
                        ) (Sub (Mul (Sub b4~36@ a4~34@) (Mul d4~40@ a4~34@)) b4~36@)
                       ) (Mul (Mul (Mul (Add a4~34@ a4~34@) (Mul a4~34@ d4~40@)) (Mul (Mul b4~36@ d4~40@) (
                           Sub c4~38@ b4~36@
                         ))
                        ) (Mul (Mul (Sub d4~40@ c4~38@) (Mul d4~40@ b4~36@)) (Mul (Mul c4~38@ b4~36@) (Mul a4~34@
                           d4~40@
                     ))))))
                     (=>
                      (= temp_4_1~1630@ (Mul (Mul (Mul (Mul (Mul b4~36@ d4~40@) (Mul a4~34@ a4~34@)) (Mul (Mul
                            d4~40@ c4~38@
                           ) (Mul b4~36@ d4~40@)
                          )
                         ) (Sub (Mul (Sub b4~36@ a4~34@) (Mul d4~40@ a4~34@)) b4~36@)
                        ) (Mul (Mul (Mul (Add a4~34@ a4~34@) (Mul a4~34@ d4~40@)) (Mul (Mul b4~36@ d4~40@) (
                            Sub c4~38@ b4~36@
                          ))
                         ) (Mul (Mul (Mul c4~38@ b4~36@) (Mul a4~34@ d4~40@)) (Mul (Sub d4~40@ c4~38@) (Mul d4~40@
                            b4~36@
                      ))))))
                      (and
                       (=>
                        (= tmp%4@ (Mul (Sub d4~40@ c4~38@) (Mul d4~40@ b4~36@)))
                        (=>
                         (= tmp%5@ (Mul (Mul c4~38@ b4~36@) (Mul a4~34@ d4~40@)))
                         (=>
                          (ens%main!nl_basics.lemma_mul_is_commutative. tmp%4@ tmp%5@)
                          (=>
                           %%location_label%%4
                           (= temp_4_0~1513@ temp_4_1~1630@)
                       ))))
                       (=>
                        (= temp_4_0~1513@ temp_4_1~1630@)
                        (=>
                         (= temp_5_0~1783@ (Mul (Sub (Sub (Mul (Mul d5~48@ d5~48@) d5~48@) (Mul (Mul c5~46@ d5~48@)
                              (Mul b5~44@ a5~42@)
                             )
                            ) (Mul a5~42@ (Mul (Mul d5~48@ a5~42@) (Mul c5~46@ a5~42@)))
                           ) (Mul (Mul (Mul a5~42@ b5~44@) (Mul (Mul c5~46@ d5~48@) (Add b5~44@ d5~48@))) (Mul
                             (Mul d5~48@ (Mul d5~48@ a5~42@)) (Sub (Mul c5~46@ c5~46@) (Mul a5~42@ d5~48@))
                         ))))
                         (=>
                          (= temp_5_1~1884@ (Mul (Sub (Sub (Mul (Mul d5~48@ d5~48@) d5~48@) (Mul (Mul c5~46@ d5~48@)
                               (Mul b5~44@ a5~42@)
                              )
                             ) (Mul a5~42@ (Mul (Mul d5~48@ a5~42@) (Mul c5~46@ a5~42@)))
                            ) (Mul (Mul (Mul a5~42@ b5~44@) (Mul (Mul c5~46@ d5~48@) (Add b5~44@ d5~48@))) (Mul
                              (Mul d5~48@ (Mul d5~48@ a5~42@)) (Sub (Mul c5~46@ c5~46@) (Mul d5~48@ a5~42@))
                          ))))
                          (and
                           (=>
                            (ens%main!nl_basics.lemma_mul_is_commutative. a5~42@ d5~48@)
                            (=>
                             %%location_label%%5
                             (= temp_5_0~1783@ temp_5_1~1884@)
                           ))
                           (=>
                            (= temp_5_0~1783@ temp_5_1~1884@)
                            (=>
                             (= temp_6_0~1997@ (Mul (Mul (Mul d6~56@ (Mul (Mul a6~50@ b6~52@) (Mul a6~50@ d6~56@)))
                                c6~54@
                               ) (Mul (Mul (Mul (Mul d6~56@ b6~52@) (Mul c6~54@ c6~54@)) (Mul (Mul b6~52@ d6~56@) (
                                   Mul c6~54@ d6~56@
                                 ))
                                ) (Mul (Mul (Mul d6~56@ b6~52@) b6~52@) (Sub (Mul b6~52@ b6~52@) (Mul b6~52@ a6~50@)))
                             )))
                             (=>
                              (= temp_6_1~2082@ (Mul (Mul (Mul (Mul d6~56@ (Mul (Mul a6~50@ b6~52@) (Mul a6~50@ d6~56@)))
                                  c6~54@
                                 ) (Mul (Mul (Mul d6~56@ b6~52@) (Mul c6~54@ c6~54@)) (Mul (Mul b6~52@ d6~56@) (Mul c6~54@
                                    d6~56@
                                 )))
                                ) (Mul (Mul (Mul d6~56@ b6~52@) b6~52@) (Sub (Mul b6~52@ b6~52@) (Mul b6~52@ a6~50@)))
                              ))
                              (and
                               (=>
                                (= tmp%6@ (Mul (Mul d6~56@ (Mul (Mul a6~50@ b6~52@) (Mul a6~50@ d6~56@))) c6~54@))
                                (=>
                                 (= tmp%7@ (Mul (Mul (Mul d6~56@ b6~52@) (Mul c6~54@ c6~54@)) (Mul (Mul b6~52@ d6~56@)
                                    (Mul c6~54@ d6~56@)
                                 )))
                                 (=>
                                  (= tmp%8@ (Mul (Mul (Mul d6~56@ b6~52@) b6~52@) (Sub (Mul b6~52@ b6~52@) (Mul b6~52@
                                      a6~50@
                                  ))))
                                  (=>
                                   (ens%main!nl_basics.lemma_mul_is_associative. tmp%6@ tmp%7@ tmp%8@)
                                   (=>
                                    %%location_label%%6
                                    (= temp_6_0~1997@ temp_6_1~2082@)
                               )))))
                               (=>
                                (= temp_6_0~1997@ temp_6_1~2082@)
                                (=>
                                 (= temp_7_0~2297@ (Sub (Sub (Mul (Mul (Mul d7~64@ a7~58@) (Mul b7~60@ d7~64@)) (Mul (Mul
                                       b7~60@ d7~64@
                                      ) (Mul d7~64@ d7~64@)
                                     )
                                    ) (Mul (Mul (Sub c7~62@ a7~58@) a7~58@) d7~64@)
                                   ) (Add (Sub (Mul (Mul a7~58@ d7~64@) (Mul d7~64@ b7~60@)) (Mul (Sub c7~62@ d7~64@) (
                                       Mul d7~64@ b7~60@
                                     ))
                                    ) (Add (Mul (Add b7~60@ b7~60@) (Mul c7~62@ c7~62@)) (Mul (Mul a7~58@ d7~64@) (Mul d7~64@
                                       b7~60@
                                 ))))))
                                 (=>
                                  (= temp_7_1~2410@ (Sub (Sub (Mul (Mul (Mul b7~60@ d7~64@) (Mul d7~64@ d7~64@)) (Mul (Mul
                                        d7~64@ a7~58@
                                       ) (Mul b7~60@ d7~64@)
                                      )
                                     ) (Mul (Mul (Sub c7~62@ a7~58@) a7~58@) d7~64@)
                                    ) (Add (Sub (Mul (Mul a7~58@ d7~64@) (Mul d7~64@ b7~60@)) (Mul (Sub c7~62@ d7~64@) (
                                        Mul d7~64@ b7~60@
                                      ))
                                     ) (Add (Mul (Add b7~60@ b7~60@) (Mul c7~62@ c7~62@)) (Mul (Mul a7~58@ d7~64@) (Mul d7~64@
                                        b7~60@
                                  ))))))
                                  (and
                                   (=>
                                    (= tmp%9@ (Mul (Mul d7~64@ a7~58@) (Mul b7~60@ d7~64@)))
                                    (=>
                                     (= tmp%10@ (Mul (Mul b7~60@ d7~64@) (Mul d7~64@ d7~64@)))
                                     (=>
                                      (ens%main!nl_basics.lemma_mul_is_commutative. tmp%9@ tmp%10@)
                                      (=>
                                       %%location_label%%7
                                       (= temp_7_0~2297@ temp_7_1~2410@)
                                   ))))
                                   (=>
                                    (= temp_7_0~2297@ temp_7_1~2410@)
                                    (=>
                                     (= temp_8_0~2547@ (Mul (Mul (Mul (Mul (Mul b8~68@ d8~72@) c8~70@) (Sub (Mul d8~72@ b8~68@)
                                          (Mul a8~66@ b8~68@)
                                         )
                                        ) (Mul (Mul (Mul a8~66@ d8~72@) (Add a8~66@ a8~66@)) (Mul (Mul d8~72@ d8~72@) (Mul a8~66@
                                           b8~68@
                                        )))
                                       ) (Mul a8~66@ (Mul b8~68@ (Mul (Mul d8~72@ a8~66@) (Add a8~66@ c8~70@))))
                                     ))
                                     (=>
                                      (= temp_8_1~2632@ (Mul (Mul (Mul (Mul b8~68@ d8~72@) (Mul c8~70@ (Sub (Mul d8~72@ b8~68@)
                                            (Mul a8~66@ b8~68@)
                                          ))
                                         ) (Mul (Mul (Mul a8~66@ d8~72@) (Add a8~66@ a8~66@)) (Mul (Mul d8~72@ d8~72@) (Mul a8~66@
                                            b8~68@
                                         )))
                                        ) (Mul a8~66@ (Mul b8~68@ (Mul (Mul d8~72@ a8~66@) (Add a8~66@ c8~70@))))
                                      ))
                                      (=>
                                       (= tmp%11@ (Mul b8~68@ d8~72@))
                                       (=>
                                        (= tmp%12@ (Sub (Mul d8~72@ b8~68@) (Mul a8~66@ b8~68@)))
                                        (=>
                                         (ens%main!nl_basics.lemma_mul_is_associative. tmp%11@ c8~70@ tmp%12@)
                                         (=>
                                          %%location_label%%8
                                          (= temp_8_0~2547@ temp_8_1~2632@)
 )))))))))))))))))))))))))))))))))))))))))
 (get-info :version)
 (assert
  %%query%%
 )
 (set-option :rlimit 4294967295)
 (check-sat)
 (set-option :rlimit 0)
(pop)
