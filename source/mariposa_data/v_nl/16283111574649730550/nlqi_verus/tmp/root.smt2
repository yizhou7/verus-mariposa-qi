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
;; mariposa_data/v_nl//16283111574649730550/nlqi_verus/src/main.rs:7:1: 26:40 (#0)
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
 (declare-const temp_0_0~273@ Int)
 (declare-const temp_0_1~386@ Int)
 (declare-const temp_1_0~563@ Int)
 (declare-const temp_1_1~692@ Int)
 (declare-const temp_2_0~891@ Int)
 (declare-const temp_2_1~1040@ Int)
 (declare-const temp_3_0~1137@ Int)
 (declare-const temp_3_1~1206@ Int)
 (declare-const temp_4_0~1359@ Int)
 (declare-const temp_4_1~1476@ Int)
 (declare-const temp_5_0~1625@ Int)
 (declare-const temp_5_1~1754@ Int)
 (declare-const temp_6_0~1909@ Int)
 (declare-const temp_6_1~2030@ Int)
 (declare-const temp_7_0~2139@ Int)
 (declare-const temp_7_1~2220@ Int)
 (declare-const temp_8_0~2301@ Int)
 (declare-const temp_8_1~2354@ Int)
 (declare-const temp_9_0~2509@ Int)
 (declare-const temp_9_1~2634@ Int)
 (declare-const temp_10_0~2769@ Int)
 (declare-const temp_10_1~2866@ Int)
 (declare-const temp_11_0~2935@ Int)
 (declare-const temp_11_1~2976@ Int)
 (declare-const temp_12_0~3153@ Int)
 (declare-const temp_12_1~3274@ Int)
 (declare-const temp_13_0~3371@ Int)
 (declare-const temp_13_1~3448@ Int)
 (declare-const temp_14_0~3607@ Int)
 (declare-const temp_14_1~3732@ Int)
 (declare-const temp_15_0~3923@ Int)
 (declare-const temp_15_1~4052@ Int)
 (declare-const temp_16_0~4197@ Int)
 (declare-const temp_16_1~4298@ Int)
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
     (= temp_0_0~273@ (Mul (Mul (Mul (Add (Mul c0~6@ a0~2@) (Mul c0~6@ b0~4@)) d0~8@) (Mul
         (Mul (Mul c0~6@ b0~4@) (Sub d0~8@ c0~6@)) (Sub (Mul a0~2@ b0~4@) (Mul d0~8@ a0~2@))
        )
       ) (Mul (Mul (Mul (Sub d0~8@ a0~2@) (Mul d0~8@ b0~4@)) (Mul (Add c0~6@ b0~4@) (Sub a0~2@
           b0~4@
         ))
        ) (Mul (Sub (Mul b0~4@ d0~8@) a0~2@) (Mul (Mul d0~8@ d0~8@) (Mul d0~8@ b0~4@)))
     )))
     (=>
      (= temp_0_1~386@ (Mul (Mul (Mul (Add (Mul c0~6@ a0~2@) (Mul c0~6@ b0~4@)) d0~8@) (Mul
          (Mul (Mul c0~6@ b0~4@) (Sub d0~8@ c0~6@)) (Sub (Mul a0~2@ b0~4@) (Mul d0~8@ a0~2@))
         )
        ) (Mul (Mul (Mul (Sub d0~8@ a0~2@) (Mul d0~8@ b0~4@)) (Mul (Add c0~6@ b0~4@) (Sub a0~2@
            b0~4@
          ))
         ) (Mul (Mul (Mul d0~8@ d0~8@) (Mul d0~8@ b0~4@)) (Sub (Mul b0~4@ d0~8@) a0~2@))
      )))
      (and
       (=>
        (= tmp%1@ (Sub (Mul b0~4@ d0~8@) a0~2@))
        (=>
         (= tmp%2@ (Mul (Mul d0~8@ d0~8@) (Mul d0~8@ b0~4@)))
         (=>
          (ens%main!nl_basics.lemma_mul_is_commutative. tmp%1@ tmp%2@)
          (=>
           %%location_label%%0
           (= temp_0_0~273@ temp_0_1~386@)
       ))))
       (=>
        (= temp_0_0~273@ temp_0_1~386@)
        (=>
         (= temp_1_0~563@ (Mul (Mul (Mul (Mul (Mul a1~10@ d1~16@) (Mul a1~10@ d1~16@)) (Mul (Mul
               c1~14@ d1~16@
              ) (Mul d1~16@ c1~14@)
             )
            ) (Mul (Sub (Add d1~16@ b1~12@) (Sub d1~16@ b1~12@)) (Mul (Mul a1~10@ c1~14@) (Add c1~14@
               b1~12@
            )))
           ) (Sub (Mul (Mul (Mul c1~14@ a1~10@) (Mul a1~10@ a1~10@)) (Mul (Mul d1~16@ b1~12@) (
               Mul a1~10@ c1~14@
             ))
            ) (Mul (Mul (Sub c1~14@ c1~14@) (Mul a1~10@ c1~14@)) (Mul (Mul c1~14@ b1~12@) (Mul a1~10@
               a1~10@
         ))))))
         (=>
          (= temp_1_1~692@ (Mul (Mul (Mul (Mul a1~10@ d1~16@) (Mul (Mul a1~10@ d1~16@) (Mul (Mul c1~14@
                 d1~16@
                ) (Mul d1~16@ c1~14@)
              ))
             ) (Mul (Sub (Add d1~16@ b1~12@) (Sub d1~16@ b1~12@)) (Mul (Mul a1~10@ c1~14@) (Add c1~14@
                b1~12@
             )))
            ) (Sub (Mul (Mul (Mul c1~14@ a1~10@) (Mul a1~10@ a1~10@)) (Mul (Mul d1~16@ b1~12@) (
                Mul a1~10@ c1~14@
              ))
             ) (Mul (Mul (Sub c1~14@ c1~14@) (Mul a1~10@ c1~14@)) (Mul (Mul c1~14@ b1~12@) (Mul a1~10@
                a1~10@
          ))))))
          (and
           (=>
            (= tmp%3@ (Mul a1~10@ d1~16@))
            (=>
             (= tmp%4@ (Mul a1~10@ d1~16@))
             (=>
              (= tmp%5@ (Mul (Mul c1~14@ d1~16@) (Mul d1~16@ c1~14@)))
              (=>
               (ens%main!nl_basics.lemma_mul_is_associative. tmp%3@ tmp%4@ tmp%5@)
               (=>
                %%location_label%%1
                (= temp_1_0~563@ temp_1_1~692@)
           )))))
           (=>
            (= temp_1_0~563@ temp_1_1~692@)
            (=>
             (= temp_2_0~891@ (Mul (Add (Mul (Mul (Mul 59 a2~18@) (Sub b2~20@ b2~20@)) (Mul (Mul b2~20@
                   a2~18@
                  ) (Mul b2~20@ d2~24@)
                 )
                ) (Mul (Sub c2~22@ (Mul c2~22@ a2~18@)) (Mul (Mul a2~18@ a2~18@) (Mul b2~20@ a2~18@)))
               ) (Sub (Mul (Mul (Mul b2~20@ c2~22@) (Mul c2~22@ a2~18@)) (Mul (Sub a2~18@ b2~20@) (
                   Mul b2~20@ d2~24@
                 ))
                ) (Mul (Mul (Mul 5 d2~24@) (Mul c2~22@ a2~18@)) (Mul (Mul d2~24@ c2~22@) (Mul c2~22@
                   a2~18@
             ))))))
             (=>
              (= temp_2_1~1040@ (Mul (Add (Mul (Mul (Mul 59 a2~18@) (Sub b2~20@ b2~20@)) (Mul (Mul b2~20@
                    a2~18@
                   ) (Mul d2~24@ b2~20@)
                  )
                 ) (Mul (Sub c2~22@ (Mul c2~22@ a2~18@)) (Mul (Mul a2~18@ a2~18@) (Mul b2~20@ a2~18@)))
                ) (Sub (Mul (Mul (Mul b2~20@ c2~22@) (Mul c2~22@ a2~18@)) (Mul (Sub a2~18@ b2~20@) (
                    Mul b2~20@ d2~24@
                  ))
                 ) (Mul (Mul (Mul 5 d2~24@) (Mul c2~22@ a2~18@)) (Mul (Mul d2~24@ c2~22@) (Mul c2~22@
                    a2~18@
              ))))))
              (and
               (=>
                (ens%main!nl_basics.lemma_mul_is_commutative. b2~20@ d2~24@)
                (=>
                 %%location_label%%2
                 (= temp_2_0~891@ temp_2_1~1040@)
               ))
               (=>
                (= temp_2_0~891@ temp_2_1~1040@)
                (=>
                 (= temp_3_0~1137@ (Sub b3~28@ (Mul (Mul (Mul (Mul d3~32@ b3~28@) (Mul a3~26@ d3~32@))
                     (Mul (Mul b3~28@ b3~28@) (Add a3~26@ b3~28@))
                    ) (Mul (Sub (Mul d3~32@ c3~30@) (Mul c3~30@ c3~30@)) (Mul (Mul b3~28@ c3~30@) (Mul b3~28@
                       b3~28@
                 ))))))
                 (=>
                  (= temp_3_1~1206@ (Sub b3~28@ (Mul (Mul (Mul (Mul a3~26@ d3~32@) (Mul d3~32@ b3~28@))
                      (Mul (Mul b3~28@ b3~28@) (Add a3~26@ b3~28@))
                     ) (Mul (Sub (Mul d3~32@ c3~30@) (Mul c3~30@ c3~30@)) (Mul (Mul b3~28@ c3~30@) (Mul b3~28@
                        b3~28@
                  ))))))
                  (and
                   (=>
                    (= tmp%6@ (Mul d3~32@ b3~28@))
                    (=>
                     (= tmp%7@ (Mul a3~26@ d3~32@))
                     (=>
                      (ens%main!nl_basics.lemma_mul_is_commutative. tmp%6@ tmp%7@)
                      (=>
                       %%location_label%%3
                       (= temp_3_0~1137@ temp_3_1~1206@)
                   ))))
                   (=>
                    (= temp_3_0~1137@ temp_3_1~1206@)
                    (=>
                     (= temp_4_0~1359@ (Mul (Mul (Mul (Mul (Mul c4~38@ d4~40@) (Sub b4~36@ b4~36@)) (Mul (Mul
                           c4~38@ a4~34@
                          ) (Mul d4~40@ b4~36@)
                         )
                        ) (Mul (Mul (Mul b4~36@ b4~36@) (Mul c4~38@ a4~34@)) (Mul (Mul a4~34@ d4~40@) (Mul c4~38@
                           a4~34@
                        )))
                       ) (Mul (Mul (Mul (Mul b4~36@ b4~36@) (Mul c4~38@ b4~36@)) d4~40@) (Mul (Add (Mul a4~34@
                           a4~34@
                          ) (Mul a4~34@ a4~34@)
                         ) (Mul (Mul b4~36@ b4~36@) (Mul a4~34@ c4~38@))
                     ))))
                     (=>
                      (= temp_4_1~1476@ (Mul (Mul (Mul (Mul (Mul c4~38@ d4~40@) (Sub b4~36@ b4~36@)) (Mul (Mul
                            c4~38@ a4~34@
                           ) (Mul d4~40@ b4~36@)
                          )
                         ) (Mul (Mul (Mul b4~36@ b4~36@) (Mul c4~38@ a4~34@)) (Mul (Mul a4~34@ d4~40@) (Mul c4~38@
                            a4~34@
                         )))
                        ) (Mul (Mul (Mul (Mul b4~36@ b4~36@) (Mul c4~38@ b4~36@)) d4~40@) (Mul (Add (Mul a4~34@
                            a4~34@
                           ) (Mul a4~34@ a4~34@)
                          ) (Mul (Mul b4~36@ b4~36@) (Mul c4~38@ a4~34@))
                      ))))
                      (and
                       (=>
                        (ens%main!nl_basics.lemma_mul_is_commutative. a4~34@ c4~38@)
                        (=>
                         %%location_label%%4
                         (= temp_4_0~1359@ temp_4_1~1476@)
                       ))
                       (=>
                        (= temp_4_0~1359@ temp_4_1~1476@)
                        (=>
                         (= temp_5_0~1625@ (Sub (Mul (Mul (Mul (Add d5~48@ d5~48@) (Mul c5~46@ b5~44@)) (Mul (Add
                               d5~48@ c5~46@
                              ) (Sub c5~46@ d5~48@)
                             )
                            ) (Mul (Mul (Mul d5~48@ b5~44@) (Add b5~44@ b5~44@)) (Mul a5~42@ (Mul b5~44@ c5~46@)))
                           ) (Mul (Sub (Mul (Mul a5~42@ d5~48@) (Mul b5~44@ b5~44@)) (Add (Add c5~46@ b5~44@) (
                               Mul a5~42@ c5~46@
                             ))
                            ) (Mul (Mul (Sub a5~42@ d5~48@) d5~48@) (Mul (Sub b5~44@ c5~46@) (Mul a5~42@ b5~44@)))
                         )))
                         (=>
                          (= temp_5_1~1754@ (Sub (Mul (Mul (Mul (Add d5~48@ d5~48@) (Mul c5~46@ b5~44@)) (Mul (Add
                                d5~48@ c5~46@
                               ) (Sub c5~46@ d5~48@)
                              )
                             ) (Mul (Mul (Mul d5~48@ b5~44@) (Add b5~44@ b5~44@)) (Mul a5~42@ (Mul b5~44@ c5~46@)))
                            ) (Mul (Sub (Mul (Mul a5~42@ d5~48@) (Mul b5~44@ b5~44@)) (Add (Add c5~46@ b5~44@) (
                                Mul a5~42@ c5~46@
                              ))
                             ) (Mul (Mul (Sub a5~42@ d5~48@) d5~48@) (Sub (Mul b5~44@ (Mul a5~42@ b5~44@)) (Mul c5~46@
                                (Mul a5~42@ b5~44@)
                          ))))))
                          (and
                           (=>
                            (= tmp%8@ (Mul a5~42@ b5~44@))
                            (=>
                             (ens%main!nl_basics.lemma_mul_is_distributive. b5~44@ c5~46@ tmp%8@)
                             (=>
                              %%location_label%%5
                              (= temp_5_0~1625@ temp_5_1~1754@)
                           )))
                           (=>
                            (= temp_5_0~1625@ temp_5_1~1754@)
                            (=>
                             (= temp_6_0~1909@ (Sub (Mul (Mul (Mul (Add c6~54@ a6~50@) (Mul b6~52@ a6~50@)) (Mul (Mul
                                   d6~56@ c6~54@
                                  ) (Mul c6~54@ c6~54@)
                                 )
                                ) (Mul (Mul (Mul c6~54@ c6~54@) (Mul d6~56@ b6~52@)) (Mul d6~56@ (Mul d6~56@ a6~50@)))
                               ) (Mul (Mul (Add (Mul b6~52@ a6~50@) (Mul b6~52@ b6~52@)) (Mul (Mul a6~50@ c6~54@) (
                                   Mul b6~52@ a6~50@
                                 ))
                                ) (Mul (Mul (Add c6~54@ a6~50@) (Mul b6~52@ d6~56@)) (Sub (Mul c6~54@ a6~50@) c6~54@))
                             )))
                             (=>
                              (= temp_6_1~2030@ (Sub (Mul (Mul (Mul (Add c6~54@ a6~50@) (Mul b6~52@ a6~50@)) (Mul (Mul
                                    d6~56@ c6~54@
                                   ) (Mul c6~54@ c6~54@)
                                  )
                                 ) (Mul (Mul (Mul c6~54@ c6~54@) (Mul d6~56@ b6~52@)) (Mul d6~56@ (Mul d6~56@ a6~50@)))
                                ) (Mul (Mul (Add (Mul b6~52@ a6~50@) (Mul b6~52@ b6~52@)) (Mul (Mul a6~50@ c6~54@) (
                                    Mul b6~52@ a6~50@
                                  ))
                                 ) (Mul (Mul (Add c6~54@ a6~50@) (Mul d6~56@ b6~52@)) (Sub (Mul c6~54@ a6~50@) c6~54@))
                              )))
                              (and
                               (=>
                                (ens%main!nl_basics.lemma_mul_is_commutative. b6~52@ d6~56@)
                                (=>
                                 %%location_label%%6
                                 (= temp_6_0~1909@ temp_6_1~2030@)
                               ))
                               (=>
                                (= temp_6_0~1909@ temp_6_1~2030@)
                                (=>
                                 (= temp_7_0~2139@ (Mul (Sub (Mul (Mul c7~62@ (Sub a7~58@ c7~62@)) (Mul (Mul a7~58@ c7~62@)
                                      (Mul c7~62@ d7~64@)
                                     )
                                    ) c7~62@
                                   ) (Add (Sub a7~58@ (Add (Sub d7~64@ b7~60@) (Mul a7~58@ a7~58@))) (Mul (Mul (Mul c7~62@
                                       b7~60@
                                      ) (Mul c7~62@ a7~58@)
                                     ) (Mul (Mul b7~60@ b7~60@) d7~64@)
                                 ))))
                                 (=>
                                  (= temp_7_1~2220@ (Mul (Sub (Mul (Mul c7~62@ (Sub a7~58@ c7~62@)) (Mul (Mul c7~62@ d7~64@)
                                       (Mul a7~58@ c7~62@)
                                      )
                                     ) c7~62@
                                    ) (Add (Sub a7~58@ (Add (Sub d7~64@ b7~60@) (Mul a7~58@ a7~58@))) (Mul (Mul (Mul c7~62@
                                        b7~60@
                                       ) (Mul c7~62@ a7~58@)
                                      ) (Mul (Mul b7~60@ b7~60@) d7~64@)
                                  ))))
                                  (and
                                   (=>
                                    (= tmp%9@ (Mul a7~58@ c7~62@))
                                    (=>
                                     (= tmp%10@ (Mul c7~62@ d7~64@))
                                     (=>
                                      (ens%main!nl_basics.lemma_mul_is_commutative. tmp%9@ tmp%10@)
                                      (=>
                                       %%location_label%%7
                                       (= temp_7_0~2139@ temp_7_1~2220@)
                                   ))))
                                   (=>
                                    (= temp_7_0~2139@ temp_7_1~2220@)
                                    (=>
                                     (= temp_8_0~2301@ (Add (Mul a8~66@ (Mul (Mul (Mul b8~68@ b8~68@) (Add b8~68@ b8~68@))
                                         (Mul (Sub b8~68@ c8~70@) (Mul d8~72@ d8~72@))
                                        )
                                       ) (Mul c8~70@ a8~66@)
                                     ))
                                     (=>
                                      (= temp_8_1~2354@ (Add (Mul a8~66@ (Mul (Add (Mul (Mul b8~68@ b8~68@) b8~68@) (Mul (Mul
                                             b8~68@ b8~68@
                                            ) b8~68@
                                           )
                                          ) (Mul (Sub b8~68@ c8~70@) (Mul d8~72@ d8~72@))
                                         )
                                        ) (Mul c8~70@ a8~66@)
                                      ))
                                      (and
                                       (=>
                                        (= tmp%11@ (Mul b8~68@ b8~68@))
                                        (=>
                                         (ens%main!nl_basics.lemma_mul_is_distributive. tmp%11@ b8~68@ b8~68@)
                                         (=>
                                          %%location_label%%8
                                          (= temp_8_0~2301@ temp_8_1~2354@)
                                       )))
                                       (=>
                                        (= temp_8_0~2301@ temp_8_1~2354@)
                                        (=>
                                         (= temp_9_0~2509@ (Mul (Add (Mul (Add (Mul b9~76@ c9~78@) (Mul b9~76@ c9~78@)) d9~80@)
                                            (Mul (Add (Add c9~78@ b9~76@) (Mul c9~78@ d9~80@)) (Mul (Sub b9~76@ b9~76@) 49))
                                           ) (Add (Mul (Mul (Mul a9~74@ b9~76@) (Mul b9~76@ a9~74@)) (Mul (Mul d9~80@ b9~76@) (
                                               Mul d9~80@ d9~80@
                                             ))
                                            ) (Mul (Mul (Sub d9~80@ a9~74@) (Mul a9~74@ c9~78@)) (Mul (Sub c9~78@ a9~74@) c9~78@))
                                         )))
                                         (=>
                                          (= temp_9_1~2634@ (Mul (Add (Add (Mul (Mul b9~76@ c9~78@) d9~80@) (Mul (Mul b9~76@ c9~78@)
                                               d9~80@
                                              )
                                             ) (Mul (Add (Add c9~78@ b9~76@) (Mul c9~78@ d9~80@)) (Mul (Sub b9~76@ b9~76@) 49))
                                            ) (Add (Mul (Mul (Mul a9~74@ b9~76@) (Mul b9~76@ a9~74@)) (Mul (Mul d9~80@ b9~76@) (
                                                Mul d9~80@ d9~80@
                                              ))
                                             ) (Mul (Mul (Sub d9~80@ a9~74@) (Mul a9~74@ c9~78@)) (Mul (Sub c9~78@ a9~74@) c9~78@))
                                          )))
                                          (and
                                           (=>
                                            (= tmp%12@ (Mul b9~76@ c9~78@))
                                            (=>
                                             (= tmp%13@ (Mul b9~76@ c9~78@))
                                             (=>
                                              (ens%main!nl_basics.lemma_mul_is_distributive. tmp%12@ tmp%13@ d9~80@)
                                              (=>
                                               %%location_label%%9
                                               (= temp_9_0~2509@ temp_9_1~2634@)
                                           ))))
                                           (=>
                                            (= temp_9_0~2509@ temp_9_1~2634@)
                                            (=>
                                             (= temp_10_0~2769@ (Mul (Mul (Mul (Sub (Mul b10~84@ a10~82@) (Mul b10~84@ d10~88@)) (
                                                  Add (Sub d10~88@ d10~88@) (Mul b10~84@ a10~82@)
                                                 )
                                                ) (Mul (Mul (Mul b10~84@ d10~88@) (Mul b10~84@ a10~82@)) (Mul (Mul b10~84@ d10~88@)
                                                  (Mul a10~82@ d10~88@)
                                                ))
                                               ) (Mul (Mul (Mul (Sub b10~84@ c10~86@) (Mul b10~84@ a10~82@)) (Mul (Mul b10~84@ a10~82@)
                                                  d10~88@
                                                 )
                                                ) d10~88@
                                             )))
                                             (=>
                                              (= temp_10_1~2866@ (Mul (Mul (Mul (Sub (Mul b10~84@ a10~82@) (Mul b10~84@ d10~88@)) (
                                                   Add (Sub d10~88@ d10~88@) (Mul b10~84@ a10~82@)
                                                  )
                                                 ) (Mul (Mul (Mul b10~84@ d10~88@) (Mul b10~84@ a10~82@)) (Mul (Mul b10~84@ d10~88@)
                                                   (Mul a10~82@ d10~88@)
                                                 ))
                                                ) (Mul (Mul (Mul (Sub b10~84@ c10~86@) (Mul b10~84@ a10~82@)) (Mul (Mul a10~82@ b10~84@)
                                                   d10~88@
                                                  )
                                                 ) d10~88@
                                              )))
                                              (and
                                               (=>
                                                (ens%main!nl_basics.lemma_mul_is_commutative. b10~84@ a10~82@)
                                                (=>
                                                 %%location_label%%10
                                                 (= temp_10_0~2769@ temp_10_1~2866@)
                                               ))
                                               (=>
                                                (= temp_10_0~2769@ temp_10_1~2866@)
                                                (=>
                                                 (= temp_11_0~2935@ (Mul (Mul (Mul (Add (Mul a11~90@ a11~90@) (Mul a11~90@ b11~92@)) (
                                                      Mul (Mul a11~90@ a11~90@) (Mul d11~96@ d11~96@)
                                                     )
                                                    ) d11~96@
                                                   ) a11~90@
                                                 ))
                                                 (=>
                                                  (= temp_11_1~2976@ (Mul (Mul d11~96@ (Mul (Add (Mul a11~90@ a11~90@) (Mul a11~90@ b11~92@))
                                                      (Mul (Mul a11~90@ a11~90@) (Mul d11~96@ d11~96@))
                                                     )
                                                    ) a11~90@
                                                  ))
                                                  (and
                                                   (=>
                                                    (= tmp%14@ (Mul (Add (Mul a11~90@ a11~90@) (Mul a11~90@ b11~92@)) (Mul (Mul a11~90@ a11~90@)
                                                       (Mul d11~96@ d11~96@)
                                                    )))
                                                    (=>
                                                     (ens%main!nl_basics.lemma_mul_is_commutative. tmp%14@ d11~96@)
                                                     (=>
                                                      %%location_label%%11
                                                      (= temp_11_0~2935@ temp_11_1~2976@)
                                                   )))
                                                   (=>
                                                    (= temp_11_0~2935@ temp_11_1~2976@)
                                                    (=>
                                                     (= temp_12_0~3153@ (Sub (Add (Mul (Mul (Mul b12~100@ a12~98@) (Mul d12~104@ b12~100@))
                                                         (Mul (Mul b12~100@ b12~100@) (Mul c12~102@ a12~98@))
                                                        ) (Mul (Mul (Mul c12~102@ c12~102@) (Add b12~100@ c12~102@)) (Mul (Mul d12~104@ a12~98@)
                                                          b12~100@
                                                        ))
                                                       ) (Mul (Mul (Add (Mul a12~98@ d12~104@) (Sub b12~100@ c12~102@)) (Mul (Mul d12~104@ d12~104@)
                                                          (Mul b12~100@ a12~98@)
                                                         )
                                                        ) (Add (Mul (Sub b12~100@ a12~98@) b12~100@) (Mul (Mul b12~100@ c12~102@) (Mul a12~98@
                                                           d12~104@
                                                     ))))))
                                                     (=>
                                                      (= temp_12_1~3274@ (Sub (Add (Mul (Mul (Mul b12~100@ a12~98@) (Mul b12~100@ d12~104@))
                                                          (Mul (Mul b12~100@ b12~100@) (Mul c12~102@ a12~98@))
                                                         ) (Mul (Mul (Mul c12~102@ c12~102@) (Add b12~100@ c12~102@)) (Mul (Mul d12~104@ a12~98@)
                                                           b12~100@
                                                         ))
                                                        ) (Mul (Mul (Add (Mul a12~98@ d12~104@) (Sub b12~100@ c12~102@)) (Mul (Mul d12~104@ d12~104@)
                                                           (Mul b12~100@ a12~98@)
                                                          )
                                                         ) (Add (Mul (Sub b12~100@ a12~98@) b12~100@) (Mul (Mul b12~100@ c12~102@) (Mul a12~98@
                                                            d12~104@
                                                      ))))))
                                                      (and
                                                       (=>
                                                        (ens%main!nl_basics.lemma_mul_is_commutative. d12~104@ b12~100@)
                                                        (=>
                                                         %%location_label%%12
                                                         (= temp_12_0~3153@ temp_12_1~3274@)
                                                       ))
                                                       (=>
                                                        (= temp_12_0~3153@ temp_12_1~3274@)
                                                        (=>
                                                         (= temp_13_0~3371@ (Mul (Mul (Mul (Mul (Mul b13~108@ a13~106@) (Mul c13~110@ a13~106@))
                                                             (Mul (Mul c13~110@ d13~112@) c13~110@)
                                                            ) d13~112@
                                                           ) (Mul (Mul (Mul (Mul a13~106@ a13~106@) (Add b13~108@ a13~106@)) (Mul (Mul a13~106@
                                                               d13~112@
                                                              ) (Add d13~112@ b13~108@)
                                                             )
                                                            ) c13~110@
                                                         )))
                                                         (=>
                                                          (= temp_13_1~3448@ (Mul (Mul (Mul (Mul (Mul b13~108@ a13~106@) (Mul c13~110@ a13~106@))
                                                              (Mul (Mul c13~110@ d13~112@) c13~110@)
                                                             ) d13~112@
                                                            ) (Mul (Mul (Mul (Mul a13~106@ a13~106@) (Add b13~108@ a13~106@)) (Add (Mul (Mul a13~106@
                                                                 d13~112@
                                                                ) d13~112@
                                                               ) (Mul (Mul a13~106@ d13~112@) b13~108@)
                                                              )
                                                             ) c13~110@
                                                          )))
                                                          (and
                                                           (=>
                                                            (= tmp%15@ (Mul a13~106@ d13~112@))
                                                            (=>
                                                             (ens%main!nl_basics.lemma_mul_is_distributive. tmp%15@ d13~112@ b13~108@)
                                                             (=>
                                                              %%location_label%%13
                                                              (= temp_13_0~3371@ temp_13_1~3448@)
                                                           )))
                                                           (=>
                                                            (= temp_13_0~3371@ temp_13_1~3448@)
                                                            (=>
                                                             (= temp_14_0~3607@ (Mul (Add (Mul (Sub (Sub d14~120@ d14~120@) (Add d14~120@ b14~116@))
                                                                 d14~120@
                                                                ) (Mul (Mul (Add d14~120@ c14~118@) c14~118@) (Mul (Mul b14~116@ c14~118@) (Mul b14~116@
                                                                   d14~120@
                                                                )))
                                                               ) (Mul (Mul (Add (Mul a14~114@ c14~118@) (Mul 46 d14~120@)) (Mul (Mul d14~120@ d14~120@)
                                                                  (Mul c14~118@ c14~118@)
                                                                 )
                                                                ) (Mul (Mul (Mul a14~114@ c14~118@) (Mul d14~120@ a14~114@)) (Mul (Mul c14~118@ a14~114@)
                                                                  (Sub c14~118@ c14~118@)
                                                             )))))
                                                             (=>
                                                              (= temp_14_1~3732@ (Mul (Add (Mul (Sub (Sub d14~120@ d14~120@) (Add d14~120@ b14~116@))
                                                                  d14~120@
                                                                 ) (Mul (Mul (Add d14~120@ c14~118@) c14~118@) (Mul (Mul b14~116@ c14~118@) (Mul b14~116@
                                                                    d14~120@
                                                                 )))
                                                                ) (Mul (Mul (Mul (Add (Mul a14~114@ c14~118@) (Mul 46 d14~120@)) (Mul d14~120@ d14~120@))
                                                                  (Mul c14~118@ c14~118@)
                                                                 ) (Mul (Mul (Mul a14~114@ c14~118@) (Mul d14~120@ a14~114@)) (Mul (Mul c14~118@ a14~114@)
                                                                   (Sub c14~118@ c14~118@)
                                                              )))))
                                                              (and
                                                               (=>
                                                                (= tmp%16@ (Add (Mul a14~114@ c14~118@) (Mul 46 d14~120@)))
                                                                (=>
                                                                 (= tmp%17@ (Mul d14~120@ d14~120@))
                                                                 (=>
                                                                  (= tmp%18@ (Mul c14~118@ c14~118@))
                                                                  (=>
                                                                   (ens%main!nl_basics.lemma_mul_is_associative. tmp%16@ tmp%17@ tmp%18@)
                                                                   (=>
                                                                    %%location_label%%14
                                                                    (= temp_14_0~3607@ temp_14_1~3732@)
                                                               )))))
                                                               (=>
                                                                (= temp_14_0~3607@ temp_14_1~3732@)
                                                                (=>
                                                                 (= temp_15_0~3923@ (Add (Add (Mul (Mul (Mul 54 c15~126@) (Mul d15~128@ c15~126@)) (Mul
                                                                      (Mul a15~122@ a15~122@) (Mul c15~126@ d15~128@)
                                                                     )
                                                                    ) (Mul c15~126@ (Mul (Mul b15~124@ c15~126@) (Mul d15~128@ b15~124@)))
                                                                   ) (Mul (Mul (Add (Mul a15~122@ c15~126@) (Mul c15~126@ a15~122@)) (Mul (Add c15~126@
                                                                       d15~128@
                                                                      ) (Mul a15~122@ d15~128@)
                                                                     )
                                                                    ) (Add (Add (Sub b15~124@ d15~128@) (Add a15~122@ c15~126@)) (Mul (Mul a15~122@ a15~122@)
                                                                      (Mul a15~122@ c15~126@)
                                                                 )))))
                                                                 (=>
                                                                  (= temp_15_1~4052@ (Add (Add (Mul (Mul (Mul 54 c15~126@) (Mul d15~128@ c15~126@)) (Mul
                                                                       (Mul a15~122@ a15~122@) (Mul c15~126@ d15~128@)
                                                                      )
                                                                     ) (Mul (Mul (Mul b15~124@ c15~126@) (Mul d15~128@ b15~124@)) c15~126@)
                                                                    ) (Mul (Mul (Add (Mul a15~122@ c15~126@) (Mul c15~126@ a15~122@)) (Mul (Add c15~126@
                                                                        d15~128@
                                                                       ) (Mul a15~122@ d15~128@)
                                                                      )
                                                                     ) (Add (Add (Sub b15~124@ d15~128@) (Add a15~122@ c15~126@)) (Mul (Mul a15~122@ a15~122@)
                                                                       (Mul a15~122@ c15~126@)
                                                                  )))))
                                                                  (and
                                                                   (=>
                                                                    (= tmp%19@ (Mul (Mul b15~124@ c15~126@) (Mul d15~128@ b15~124@)))
                                                                    (=>
                                                                     (ens%main!nl_basics.lemma_mul_is_commutative. c15~126@ tmp%19@)
                                                                     (=>
                                                                      %%location_label%%15
                                                                      (= temp_15_0~3923@ temp_15_1~4052@)
                                                                   )))
                                                                   (=>
                                                                    (= temp_15_0~3923@ temp_15_1~4052@)
                                                                    (=>
                                                                     (= temp_16_0~4197@ (Mul (Mul (Add (Mul (Mul c16~134@ a16~130@) (Mul c16~134@ b16~132@))
                                                                         (Sub (Mul d16~136@ a16~130@) (Mul a16~130@ b16~132@))
                                                                        ) (Mul (Mul (Mul c16~134@ a16~130@) (Mul c16~134@ c16~134@)) (Sub (Mul c16~134@ c16~134@)
                                                                          (Mul b16~132@ c16~134@)
                                                                        ))
                                                                       ) (Mul (Add (Mul d16~136@ (Mul a16~130@ c16~134@)) (Mul (Mul b16~132@ c16~134@) d16~136@))
                                                                        (Add c16~134@ (Sub a16~130@ (Mul a16~130@ d16~136@)))
                                                                     )))
                                                                     (=>
                                                                      (= temp_16_1~4298@ (Mul (Mul (Add (Mul (Mul c16~134@ a16~130@) (Mul c16~134@ b16~132@))
                                                                          (Sub (Mul d16~136@ a16~130@) (Mul a16~130@ b16~132@))
                                                                         ) (Mul (Mul (Mul c16~134@ a16~130@) (Mul c16~134@ c16~134@)) (Mul (Sub c16~134@ b16~132@)
                                                                           c16~134@
                                                                         ))
                                                                        ) (Mul (Add (Mul d16~136@ (Mul a16~130@ c16~134@)) (Mul (Mul b16~132@ c16~134@) d16~136@))
                                                                         (Add c16~134@ (Sub a16~130@ (Mul a16~130@ d16~136@)))
                                                                      )))
                                                                      (=>
                                                                       (ens%main!nl_basics.lemma_mul_is_distributive. c16~134@ b16~132@ c16~134@)
                                                                       (=>
                                                                        %%location_label%%16
                                                                        (= temp_16_0~4197@ temp_16_1~4298@)
 )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
 (get-info :version)
 (assert
  %%query%%
 )
 (set-option :rlimit 4294967295)
 (check-sat)
 (set-option :rlimit 0)
(pop)
