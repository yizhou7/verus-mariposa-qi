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
;; mariposa_data/v_nl//9036217941583833476/nlqi_verus/src/main.rs:7:1: 26:40 (#0)
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
 (declare-const temp_0_0~297@ Int)
 (declare-const temp_0_1~434@ Int)
 (declare-const temp_1_0~615@ Int)
 (declare-const temp_1_1~736@ Int)
 (declare-const temp_2_0~917@ Int)
 (declare-const temp_2_1~1054@ Int)
 (declare-const temp_3_0~1189@ Int)
 (declare-const temp_3_1~1290@ Int)
 (declare-const temp_4_0~1449@ Int)
 (declare-const temp_4_1~1574@ Int)
 (declare-const temp_5_0~1731@ Int)
 (declare-const temp_5_1~1860@ Int)
 (declare-const temp_6_0~2001@ Int)
 (declare-const temp_6_1~2114@ Int)
 (declare-const temp_7_0~2265@ Int)
 (declare-const temp_7_1~2370@ Int)
 (declare-const temp_8_0~2517@ Int)
 (declare-const temp_8_1~2594@ Int)
 (declare-const temp_9_0~2749@ Int)
 (declare-const temp_9_1~2870@ Int)
 (declare-const temp_10_0~3011@ Int)
 (declare-const temp_10_1~3124@ Int)
 (declare-const temp_11_0~3269@ Int)
 (declare-const temp_11_1~3386@ Int)
 (declare-const temp_12_0~3645@ Int)
 (declare-const temp_12_1~3770@ Int)
 (declare-const temp_13_0~3915@ Int)
 (declare-const temp_13_1~4024@ Int)
 (declare-const temp_14_0~4197@ Int)
 (declare-const temp_14_1~4342@ Int)
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
     (= temp_0_0~297@ (Sub (Mul (Add (Mul (Mul a0~2@ d0~8@) (Mul b0~4@ d0~8@)) (Mul (Mul a0~2@
           c0~6@
          ) (Mul c0~6@ a0~2@)
         )
        ) (Add (Mul (Mul b0~4@ b0~4@) (Mul a0~2@ d0~8@)) (Mul (Mul d0~8@ d0~8@) (Mul d0~8@ d0~8@)))
       ) (Sub (Mul (Sub (Mul b0~4@ b0~4@) (Mul b0~4@ c0~6@)) (Mul d0~8@ (Sub 88 d0~8@)))
        (Mul (Sub (Mul b0~4@ c0~6@) (Mul d0~8@ d0~8@)) (Mul (Sub a0~2@ b0~4@) (Add b0~4@ d0~8@)))
     )))
     (=>
      (= temp_0_1~434@ (Sub (Mul (Add (Mul (Mul a0~2@ d0~8@) (Mul b0~4@ d0~8@)) (Mul (Mul a0~2@
            c0~6@
           ) (Mul c0~6@ a0~2@)
          )
         ) (Add (Mul (Mul b0~4@ b0~4@) (Mul a0~2@ d0~8@)) (Mul (Mul d0~8@ d0~8@) (Mul d0~8@ d0~8@)))
        ) (Sub (Mul (Mul d0~8@ (Sub 88 d0~8@)) (Sub (Mul b0~4@ b0~4@) (Mul b0~4@ c0~6@)))
         (Mul (Sub (Mul b0~4@ c0~6@) (Mul d0~8@ d0~8@)) (Mul (Sub a0~2@ b0~4@) (Add b0~4@ d0~8@)))
      )))
      (and
       (=>
        (= tmp%1@ (Sub (Mul b0~4@ b0~4@) (Mul b0~4@ c0~6@)))
        (=>
         (= tmp%2@ (Mul d0~8@ (Sub 88 d0~8@)))
         (=>
          (ens%main!nl_basics.lemma_mul_is_commutative. tmp%1@ tmp%2@)
          (=>
           %%location_label%%0
           (= temp_0_0~297@ temp_0_1~434@)
       ))))
       (=>
        (= temp_0_0~297@ temp_0_1~434@)
        (=>
         (= temp_1_0~615@ (Mul (Mul (Mul (Mul (Add a1~10@ b1~12@) (Mul a1~10@ d1~16@)) (Mul (Mul
               2 c1~14@
              ) (Mul b1~12@ a1~10@)
             )
            ) (Sub (Mul (Mul b1~12@ b1~12@) a1~10@) a1~10@)
           ) (Mul (Mul (Mul (Mul a1~10@ a1~10@) b1~12@) (Mul (Mul c1~14@ d1~16@) (Sub a1~10@ a1~10@)))
            (Mul (Mul (Mul c1~14@ c1~14@) (Mul b1~12@ b1~12@)) (Sub (Mul d1~16@ c1~14@) (Mul d1~16@
               a1~10@
         ))))))
         (=>
          (= temp_1_1~736@ (Mul (Mul (Mul (Mul (Add a1~10@ b1~12@) (Mul a1~10@ d1~16@)) (Mul (Mul
                2 c1~14@
               ) (Mul b1~12@ a1~10@)
              )
             ) (Sub (Mul (Mul b1~12@ b1~12@) a1~10@) a1~10@)
            ) (Mul (Mul (Mul (Mul a1~10@ a1~10@) b1~12@) (Mul (Mul c1~14@ d1~16@) (Sub a1~10@ a1~10@)))
             (Mul (Sub (Mul d1~16@ c1~14@) (Mul d1~16@ a1~10@)) (Mul (Mul c1~14@ c1~14@) (Mul b1~12@
                b1~12@
          ))))))
          (and
           (=>
            (= tmp%3@ (Mul (Mul c1~14@ c1~14@) (Mul b1~12@ b1~12@)))
            (=>
             (= tmp%4@ (Sub (Mul d1~16@ c1~14@) (Mul d1~16@ a1~10@)))
             (=>
              (ens%main!nl_basics.lemma_mul_is_commutative. tmp%3@ tmp%4@)
              (=>
               %%location_label%%1
               (= temp_1_0~615@ temp_1_1~736@)
           ))))
           (=>
            (= temp_1_0~615@ temp_1_1~736@)
            (=>
             (= temp_2_0~917@ (Mul (Mul (Mul (Mul (Mul a2~18@ a2~18@) (Mul b2~20@ b2~20@)) (Mul (Mul
                   a2~18@ b2~20@
                  ) (Mul c2~22@ a2~18@)
                 )
                ) (Mul (Mul (Mul c2~22@ a2~18@) (Mul a2~18@ a2~18@)) (Mul (Sub c2~22@ d2~24@) (Sub c2~22@
                   d2~24@
                )))
               ) (Sub (Mul (Mul (Mul a2~18@ d2~24@) (Mul b2~20@ b2~20@)) (Mul (Mul a2~18@ b2~20@) (
                   Mul a2~18@ c2~22@
                 ))
                ) (Mul (Mul (Mul a2~18@ b2~20@) (Mul a2~18@ a2~18@)) (Mul (Mul c2~22@ a2~18@) (Add b2~20@
                   b2~20@
             ))))))
             (=>
              (= temp_2_1~1054@ (Mul (Mul (Mul (Mul (Mul a2~18@ a2~18@) (Mul b2~20@ b2~20@)) (Mul (Mul
                    a2~18@ b2~20@
                   ) (Mul c2~22@ a2~18@)
                  )
                 ) (Mul (Mul (Mul c2~22@ a2~18@) (Mul a2~18@ a2~18@)) (Sub (Mul (Sub c2~22@ d2~24@) c2~22@)
                   (Mul (Sub c2~22@ d2~24@) d2~24@)
                 ))
                ) (Sub (Mul (Mul (Mul a2~18@ d2~24@) (Mul b2~20@ b2~20@)) (Mul (Mul a2~18@ b2~20@) (
                    Mul a2~18@ c2~22@
                  ))
                 ) (Mul (Mul (Mul a2~18@ b2~20@) (Mul a2~18@ a2~18@)) (Mul (Mul c2~22@ a2~18@) (Add b2~20@
                    b2~20@
              ))))))
              (and
               (=>
                (= tmp%5@ (Sub c2~22@ d2~24@))
                (=>
                 (ens%main!nl_basics.lemma_mul_is_distributive. tmp%5@ c2~22@ d2~24@)
                 (=>
                  %%location_label%%2
                  (= temp_2_0~917@ temp_2_1~1054@)
               )))
               (=>
                (= temp_2_0~917@ temp_2_1~1054@)
                (=>
                 (= temp_3_0~1189@ (Mul (Add (Sub (Mul (Mul a3~26@ d3~32@) (Mul a3~26@ c3~30@)) (Mul (Mul
                       a3~26@ c3~30@
                      ) (Mul c3~30@ a3~26@)
                     )
                    ) (Mul (Mul (Mul c3~30@ c3~30@) (Sub a3~26@ d3~32@)) (Mul (Add b3~28@ b3~28@) (Mul a3~26@
                       a3~26@
                    )))
                   ) (Mul c3~30@ (Sub (Mul (Mul d3~32@ d3~32@) (Mul c3~30@ d3~32@)) (Mul (Sub a3~26@ a3~26@)
                      (Add b3~28@ c3~30@)
                 )))))
                 (=>
                  (= temp_3_1~1290@ (Mul (Add (Sub (Mul (Mul a3~26@ d3~32@) (Mul a3~26@ c3~30@)) (Mul (Mul
                        a3~26@ c3~30@
                       ) (Mul c3~30@ a3~26@)
                      )
                     ) (Mul (Mul (Mul c3~30@ c3~30@) (Sub a3~26@ d3~32@)) (Mul (Mul (Add b3~28@ b3~28@) a3~26@)
                       a3~26@
                     ))
                    ) (Mul c3~30@ (Sub (Mul (Mul d3~32@ d3~32@) (Mul c3~30@ d3~32@)) (Mul (Sub a3~26@ a3~26@)
                       (Add b3~28@ c3~30@)
                  )))))
                  (and
                   (=>
                    (= tmp%6@ (Add b3~28@ b3~28@))
                    (=>
                     (ens%main!nl_basics.lemma_mul_is_associative. tmp%6@ a3~26@ a3~26@)
                     (=>
                      %%location_label%%3
                      (= temp_3_0~1189@ temp_3_1~1290@)
                   )))
                   (=>
                    (= temp_3_0~1189@ temp_3_1~1290@)
                    (=>
                     (= temp_4_0~1449@ (Mul (Sub (Mul (Mul (Mul c4~38@ c4~38@) (Mul c4~38@ b4~36@)) (Mul (Mul
                           c4~38@ c4~38@
                          ) b4~36@
                         )
                        ) (Mul (Mul (Mul b4~36@ d4~40@) (Mul b4~36@ a4~34@)) c4~38@)
                       ) (Add (Add (Mul (Mul a4~34@ 50) (Mul b4~36@ b4~36@)) (Mul (Mul b4~36@ c4~38@) (Mul c4~38@
                           c4~38@
                         ))
                        ) (Sub (Mul (Add c4~38@ d4~40@) (Mul a4~34@ c4~38@)) (Add (Sub d4~40@ c4~38@) (Mul c4~38@
                           d4~40@
                     ))))))
                     (=>
                      (= temp_4_1~1574@ (Mul (Sub (Mul (Mul (Mul c4~38@ c4~38@) (Mul c4~38@ b4~36@)) (Mul (Mul
                            c4~38@ c4~38@
                           ) b4~36@
                          )
                         ) (Mul (Mul (Mul b4~36@ d4~40@) (Mul b4~36@ a4~34@)) c4~38@)
                        ) (Add (Add (Mul (Mul a4~34@ 50) (Mul b4~36@ b4~36@)) (Mul (Mul b4~36@ c4~38@) (Mul c4~38@
                            c4~38@
                          ))
                         ) (Sub (Mul (Add c4~38@ d4~40@) (Mul c4~38@ a4~34@)) (Add (Sub d4~40@ c4~38@) (Mul c4~38@
                            d4~40@
                      ))))))
                      (and
                       (=>
                        (ens%main!nl_basics.lemma_mul_is_commutative. a4~34@ c4~38@)
                        (=>
                         %%location_label%%4
                         (= temp_4_0~1449@ temp_4_1~1574@)
                       ))
                       (=>
                        (= temp_4_0~1449@ temp_4_1~1574@)
                        (=>
                         (= temp_5_0~1731@ (Mul (Mul (Mul (Mul (Mul b5~44@ a5~42@) (Mul c5~46@ b5~44@)) (Mul (Mul
                               a5~42@ d5~48@
                              ) (Mul b5~44@ b5~44@)
                             )
                            ) (Mul (Mul (Mul c5~46@ d5~48@) (Mul c5~46@ b5~44@)) (Mul (Mul d5~48@ b5~44@) (Mul d5~48@
                               d5~48@
                            )))
                           ) (Mul (Mul (Mul (Mul c5~46@ b5~44@) (Add c5~46@ c5~46@)) (Mul (Mul b5~44@ d5~48@) (
                               Add d5~48@ a5~42@
                             ))
                            ) (Mul (Mul (Mul c5~46@ c5~46@) (Mul c5~46@ d5~48@)) (Mul (Mul d5~48@ b5~44@) (Mul d5~48@
                               d5~48@
                         ))))))
                         (=>
                          (= temp_5_1~1860@ (Mul (Mul (Mul (Mul (Mul a5~42@ b5~44@) (Mul c5~46@ b5~44@)) (Mul (Mul
                                a5~42@ d5~48@
                               ) (Mul b5~44@ b5~44@)
                              )
                             ) (Mul (Mul (Mul c5~46@ d5~48@) (Mul c5~46@ b5~44@)) (Mul (Mul d5~48@ b5~44@) (Mul d5~48@
                                d5~48@
                             )))
                            ) (Mul (Mul (Mul (Mul c5~46@ b5~44@) (Add c5~46@ c5~46@)) (Mul (Mul b5~44@ d5~48@) (
                                Add d5~48@ a5~42@
                              ))
                             ) (Mul (Mul (Mul c5~46@ c5~46@) (Mul c5~46@ d5~48@)) (Mul (Mul d5~48@ b5~44@) (Mul d5~48@
                                d5~48@
                          ))))))
                          (and
                           (=>
                            (ens%main!nl_basics.lemma_mul_is_commutative. b5~44@ a5~42@)
                            (=>
                             %%location_label%%5
                             (= temp_5_0~1731@ temp_5_1~1860@)
                           ))
                           (=>
                            (= temp_5_0~1731@ temp_5_1~1860@)
                            (=>
                             (= temp_6_0~2001@ (Mul (Mul (Mul (Mul (Mul b6~52@ d6~56@) (Mul b6~52@ d6~56@)) (Sub c6~54@
                                  (Mul d6~56@ d6~56@)
                                 )
                                ) (Add (Mul b6~52@ (Mul a6~50@ d6~56@)) (Mul (Add b6~52@ d6~56@) (Mul d6~56@ c6~54@)))
                               ) (Mul (Mul (Mul (Sub d6~56@ d6~56@) c6~54@) (Mul c6~54@ (Mul a6~50@ d6~56@))) (Mul
                                 (Mul (Add d6~56@ b6~52@) (Mul c6~54@ a6~50@)) (Mul (Mul b6~52@ b6~52@) (Mul c6~54@
                                   d6~56@
                             ))))))
                             (=>
                              (= temp_6_1~2114@ (Mul (Mul (Mul (Mul b6~52@ d6~56@) (Mul (Mul b6~52@ d6~56@) (Sub c6~54@
                                    (Mul d6~56@ d6~56@)
                                  ))
                                 ) (Add (Mul b6~52@ (Mul a6~50@ d6~56@)) (Mul (Add b6~52@ d6~56@) (Mul d6~56@ c6~54@)))
                                ) (Mul (Mul (Mul (Sub d6~56@ d6~56@) c6~54@) (Mul c6~54@ (Mul a6~50@ d6~56@))) (Mul
                                  (Mul (Add d6~56@ b6~52@) (Mul c6~54@ a6~50@)) (Mul (Mul b6~52@ b6~52@) (Mul c6~54@
                                    d6~56@
                              ))))))
                              (and
                               (=>
                                (= tmp%7@ (Mul b6~52@ d6~56@))
                                (=>
                                 (= tmp%8@ (Mul b6~52@ d6~56@))
                                 (=>
                                  (= tmp%9@ (Sub c6~54@ (Mul d6~56@ d6~56@)))
                                  (=>
                                   (ens%main!nl_basics.lemma_mul_is_associative. tmp%7@ tmp%8@ tmp%9@)
                                   (=>
                                    %%location_label%%6
                                    (= temp_6_0~2001@ temp_6_1~2114@)
                               )))))
                               (=>
                                (= temp_6_0~2001@ temp_6_1~2114@)
                                (=>
                                 (= temp_7_0~2265@ (Mul (Mul (Mul (Mul (Mul d7~64@ b7~60@) (Mul d7~64@ a7~58@)) (Mul (Mul
                                       b7~60@ c7~62@
                                      ) (Mul c7~62@ b7~60@)
                                     )
                                    ) (Sub (Add (Mul a7~58@ b7~60@) d7~64@) (Mul (Mul d7~64@ a7~58@) (Mul b7~60@ d7~64@)))
                                   ) (Mul (Mul (Add (Sub b7~60@ b7~60@) (Mul c7~62@ a7~58@)) (Mul (Mul a7~58@ b7~60@) d7~64@))
                                    (Mul b7~60@ (Sub a7~58@ (Mul c7~62@ d7~64@)))
                                 )))
                                 (=>
                                  (= temp_7_1~2370@ (Mul (Mul (Mul (Mul d7~64@ b7~60@) (Mul d7~64@ a7~58@)) (Mul (Mul (Mul
                                        b7~60@ c7~62@
                                       ) (Mul c7~62@ b7~60@)
                                      ) (Sub (Add (Mul a7~58@ b7~60@) d7~64@) (Mul (Mul d7~64@ a7~58@) (Mul b7~60@ d7~64@)))
                                     )
                                    ) (Mul (Mul (Add (Sub b7~60@ b7~60@) (Mul c7~62@ a7~58@)) (Mul (Mul a7~58@ b7~60@) d7~64@))
                                     (Mul b7~60@ (Sub a7~58@ (Mul c7~62@ d7~64@)))
                                  )))
                                  (and
                                   (=>
                                    (= tmp%10@ (Mul (Mul d7~64@ b7~60@) (Mul d7~64@ a7~58@)))
                                    (=>
                                     (= tmp%11@ (Mul (Mul b7~60@ c7~62@) (Mul c7~62@ b7~60@)))
                                     (=>
                                      (= tmp%12@ (Sub (Add (Mul a7~58@ b7~60@) d7~64@) (Mul (Mul d7~64@ a7~58@) (Mul b7~60@
                                          d7~64@
                                      ))))
                                      (=>
                                       (ens%main!nl_basics.lemma_mul_is_associative. tmp%10@ tmp%11@ tmp%12@)
                                       (=>
                                        %%location_label%%7
                                        (= temp_7_0~2265@ temp_7_1~2370@)
                                   )))))
                                   (=>
                                    (= temp_7_0~2265@ temp_7_1~2370@)
                                    (=>
                                     (= temp_8_0~2517@ (Mul b8~68@ (Mul (Add (Add (Mul a8~66@ b8~68@) (Mul a8~66@ b8~68@))
                                         (Mul (Sub b8~68@ c8~70@) (Mul d8~72@ d8~72@))
                                        ) (Mul (Mul (Mul d8~72@ b8~68@) (Mul c8~70@ b8~68@)) (Mul (Mul d8~72@ d8~72@) (Mul b8~68@
                                           b8~68@
                                     ))))))
                                     (=>
                                      (= temp_8_1~2594@ (Mul b8~68@ (Mul (Add (Add (Mul a8~66@ b8~68@) (Mul a8~66@ b8~68@))
                                          (Sub (Mul b8~68@ (Mul d8~72@ d8~72@)) (Mul c8~70@ (Mul d8~72@ d8~72@)))
                                         ) (Mul (Mul (Mul d8~72@ b8~68@) (Mul c8~70@ b8~68@)) (Mul (Mul d8~72@ d8~72@) (Mul b8~68@
                                            b8~68@
                                      ))))))
                                      (and
                                       (=>
                                        (= tmp%13@ (Mul d8~72@ d8~72@))
                                        (=>
                                         (ens%main!nl_basics.lemma_mul_is_distributive. b8~68@ c8~70@ tmp%13@)
                                         (=>
                                          %%location_label%%8
                                          (= temp_8_0~2517@ temp_8_1~2594@)
                                       )))
                                       (=>
                                        (= temp_8_0~2517@ temp_8_1~2594@)
                                        (=>
                                         (= temp_9_0~2749@ (Add (Mul (Add (Mul (Mul a9~74@ c9~78@) (Mul c9~78@ b9~76@)) (Mul (Mul
                                               c9~78@ c9~78@
                                              ) (Mul a9~74@ a9~74@)
                                             )
                                            ) (Sub (Mul (Add a9~74@ c9~78@) a9~74@) (Mul (Mul b9~76@ c9~78@) (Add b9~76@ a9~74@)))
                                           ) (Mul (Mul (Add (Mul d9~80@ b9~76@) (Mul d9~80@ b9~76@)) (Mul (Add b9~76@ b9~76@) (
                                               Add b9~76@ a9~74@
                                             ))
                                            ) (Mul (Add (Mul d9~80@ d9~80@) b9~76@) (Mul (Mul d9~80@ b9~76@) (Mul b9~76@ d9~80@)))
                                         )))
                                         (=>
                                          (= temp_9_1~2870@ (Add (Mul (Add (Mul (Mul a9~74@ c9~78@) (Mul c9~78@ b9~76@)) (Mul (Mul
                                                c9~78@ c9~78@
                                               ) (Mul a9~74@ a9~74@)
                                              )
                                             ) (Sub (Mul (Add a9~74@ c9~78@) a9~74@) (Mul (Mul b9~76@ c9~78@) (Add b9~76@ a9~74@)))
                                            ) (Mul (Mul (Add (Mul d9~80@ b9~76@) (Mul d9~80@ b9~76@)) (Mul (Add b9~76@ b9~76@) (
                                                Add b9~76@ a9~74@
                                              ))
                                             ) (Mul (Add (Mul d9~80@ d9~80@) b9~76@) (Mul (Mul d9~80@ b9~76@) (Mul d9~80@ b9~76@)))
                                          )))
                                          (and
                                           (=>
                                            (ens%main!nl_basics.lemma_mul_is_commutative. b9~76@ d9~80@)
                                            (=>
                                             %%location_label%%9
                                             (= temp_9_0~2749@ temp_9_1~2870@)
                                           ))
                                           (=>
                                            (= temp_9_0~2749@ temp_9_1~2870@)
                                            (=>
                                             (= temp_10_0~3011@ (Add (Mul (Mul (Add (Mul a10~82@ b10~84@) (Mul a10~82@ b10~84@)) (
                                                  Mul b10~84@ (Add a10~82@ a10~82@)
                                                 )
                                                ) (Mul (Mul (Mul b10~84@ 4) (Sub b10~84@ c10~86@)) (Mul (Mul d10~88@ d10~88@) (Mul b10~84@
                                                   b10~84@
                                                )))
                                               ) (Mul (Mul b10~84@ (Mul (Mul c10~86@ d10~88@) (Mul c10~86@ a10~82@))) (Add (Mul (Mul
                                                   a10~82@ c10~86@
                                                  ) (Mul d10~88@ a10~82@)
                                                 ) c10~86@
                                             ))))
                                             (=>
                                              (= temp_10_1~3124@ (Add (Mul (Mul (Add (Mul a10~82@ b10~84@) (Mul b10~84@ a10~82@)) (
                                                   Mul b10~84@ (Add a10~82@ a10~82@)
                                                  )
                                                 ) (Mul (Mul (Mul b10~84@ 4) (Sub b10~84@ c10~86@)) (Mul (Mul d10~88@ d10~88@) (Mul b10~84@
                                                    b10~84@
                                                 )))
                                                ) (Mul (Mul b10~84@ (Mul (Mul c10~86@ d10~88@) (Mul c10~86@ a10~82@))) (Add (Mul (Mul
                                                    a10~82@ c10~86@
                                                   ) (Mul d10~88@ a10~82@)
                                                  ) c10~86@
                                              ))))
                                              (and
                                               (=>
                                                (ens%main!nl_basics.lemma_mul_is_commutative. a10~82@ b10~84@)
                                                (=>
                                                 %%location_label%%10
                                                 (= temp_10_0~3011@ temp_10_1~3124@)
                                               ))
                                               (=>
                                                (= temp_10_0~3011@ temp_10_1~3124@)
                                                (=>
                                                 (= temp_11_0~3269@ (Mul (Mul (Mul (Mul (Mul d11~96@ a11~90@) (Mul c11~94@ a11~90@)) (
                                                      Mul (Mul d11~96@ b11~92@) (Mul c11~94@ b11~92@)
                                                     )
                                                    ) (Mul (Mul (Mul a11~90@ c11~94@) (Mul a11~90@ c11~94@)) (Mul (Sub d11~96@ a11~90@)
                                                      (Mul b11~92@ a11~90@)
                                                    ))
                                                   ) (Add (Mul d11~96@ (Mul (Sub c11~94@ b11~92@) (Mul c11~94@ c11~94@))) (Add (Add (Mul
                                                       b11~92@ b11~92@
                                                      ) (Mul a11~90@ c11~94@)
                                                     ) (Mul (Mul d11~96@ c11~94@) (Mul d11~96@ c11~94@))
                                                 ))))
                                                 (=>
                                                  (= temp_11_1~3386@ (Mul (Mul (Mul (Mul d11~96@ a11~90@) (Mul c11~94@ a11~90@)) (Mul (
                                                       Mul d11~96@ b11~92@
                                                      ) (Mul c11~94@ b11~92@)
                                                     )
                                                    ) (Mul (Mul (Mul (Mul a11~90@ c11~94@) (Mul a11~90@ c11~94@)) (Mul (Sub d11~96@ a11~90@)
                                                       (Mul b11~92@ a11~90@)
                                                      )
                                                     ) (Add (Mul d11~96@ (Mul (Sub c11~94@ b11~92@) (Mul c11~94@ c11~94@))) (Add (Add (Mul
                                                         b11~92@ b11~92@
                                                        ) (Mul a11~90@ c11~94@)
                                                       ) (Mul (Mul d11~96@ c11~94@) (Mul d11~96@ c11~94@))
                                                  )))))
                                                  (and
                                                   (=>
                                                    (= tmp%14@ (Mul (Mul (Mul d11~96@ a11~90@) (Mul c11~94@ a11~90@)) (Mul (Mul d11~96@ b11~92@)
                                                       (Mul c11~94@ b11~92@)
                                                    )))
                                                    (=>
                                                     (= tmp%15@ (Mul (Mul (Mul a11~90@ c11~94@) (Mul a11~90@ c11~94@)) (Mul (Sub d11~96@ a11~90@)
                                                        (Mul b11~92@ a11~90@)
                                                     )))
                                                     (=>
                                                      (= tmp%16@ (Add (Mul d11~96@ (Mul (Sub c11~94@ b11~92@) (Mul c11~94@ c11~94@))) (Add
                                                         (Add (Mul b11~92@ b11~92@) (Mul a11~90@ c11~94@)) (Mul (Mul d11~96@ c11~94@) (Mul d11~96@
                                                           c11~94@
                                                      )))))
                                                      (=>
                                                       (ens%main!nl_basics.lemma_mul_is_associative. tmp%14@ tmp%15@ tmp%16@)
                                                       (=>
                                                        %%location_label%%11
                                                        (= temp_11_0~3269@ temp_11_1~3386@)
                                                   )))))
                                                   (=>
                                                    (= temp_11_0~3269@ temp_11_1~3386@)
                                                    (=>
                                                     (= temp_12_0~3645@ (Sub (Mul (Mul (Mul (Mul c12~102@ c12~102@) (Mul a12~98@ b12~100@))
                                                         (Mul (Mul c12~102@ b12~100@) (Add b12~100@ a12~98@))
                                                        ) (Mul (Mul c12~102@ (Add a12~98@ b12~100@)) (Add (Mul b12~100@ c12~102@) (Mul a12~98@
                                                           c12~102@
                                                        )))
                                                       ) (Mul (Mul (Mul (Mul d12~104@ b12~100@) (Mul b12~100@ c12~102@)) (Mul (Mul c12~102@
                                                           b12~100@
                                                          ) (Mul c12~102@ a12~98@)
                                                         )
                                                        ) (Mul (Mul (Add d12~104@ a12~98@) (Sub a12~98@ d12~104@)) (Mul (Mul b12~100@ b12~100@)
                                                          (Mul d12~104@ c12~102@)
                                                     )))))
                                                     (=>
                                                      (= temp_12_1~3770@ (Sub (Mul (Mul (Mul (Mul c12~102@ c12~102@) (Mul a12~98@ b12~100@))
                                                          (Mul (Mul c12~102@ b12~100@) (Add b12~100@ a12~98@))
                                                         ) (Mul (Mul c12~102@ (Add a12~98@ b12~100@)) (Add (Mul b12~100@ c12~102@) (Mul a12~98@
                                                            c12~102@
                                                         )))
                                                        ) (Mul (Mul (Mul (Mul b12~100@ c12~102@) (Mul d12~104@ b12~100@)) (Mul (Mul c12~102@
                                                            b12~100@
                                                           ) (Mul c12~102@ a12~98@)
                                                          )
                                                         ) (Mul (Mul (Add d12~104@ a12~98@) (Sub a12~98@ d12~104@)) (Mul (Mul b12~100@ b12~100@)
                                                           (Mul d12~104@ c12~102@)
                                                      )))))
                                                      (and
                                                       (=>
                                                        (= tmp%17@ (Mul d12~104@ b12~100@))
                                                        (=>
                                                         (= tmp%18@ (Mul b12~100@ c12~102@))
                                                         (=>
                                                          (ens%main!nl_basics.lemma_mul_is_commutative. tmp%17@ tmp%18@)
                                                          (=>
                                                           %%location_label%%12
                                                           (= temp_12_0~3645@ temp_12_1~3770@)
                                                       ))))
                                                       (=>
                                                        (= temp_12_0~3645@ temp_12_1~3770@)
                                                        (=>
                                                         (= temp_13_0~3915@ (Mul (Mul (Mul (Sub (Add b13~108@ b13~108@) (Mul b13~108@ a13~106@))
                                                             (Mul (Mul d13~112@ d13~112@) (Mul c13~110@ b13~108@))
                                                            ) (Mul (Mul (Mul a13~106@ b13~108@) (Mul d13~112@ a13~106@)) (Sub (Mul c13~110@ d13~112@)
                                                              (Mul a13~106@ a13~106@)
                                                            ))
                                                           ) (Mul (Mul (Mul (Sub a13~106@ c13~110@) (Sub c13~110@ d13~112@)) a13~106@) (Mul (Add
                                                              b13~108@ (Mul d13~112@ d13~112@)
                                                             ) (Mul c13~110@ (Mul a13~106@ b13~108@))
                                                         ))))
                                                         (=>
                                                          (= temp_13_1~4024@ (Mul (Mul (Mul (Sub (Add b13~108@ b13~108@) (Mul b13~108@ a13~106@))
                                                              (Mul (Mul d13~112@ d13~112@) (Mul c13~110@ b13~108@))
                                                             ) (Mul (Mul (Mul a13~106@ b13~108@) (Mul a13~106@ d13~112@)) (Sub (Mul c13~110@ d13~112@)
                                                               (Mul a13~106@ a13~106@)
                                                             ))
                                                            ) (Mul (Mul (Mul (Sub a13~106@ c13~110@) (Sub c13~110@ d13~112@)) a13~106@) (Mul (Add
                                                               b13~108@ (Mul d13~112@ d13~112@)
                                                              ) (Mul c13~110@ (Mul a13~106@ b13~108@))
                                                          ))))
                                                          (and
                                                           (=>
                                                            (ens%main!nl_basics.lemma_mul_is_commutative. d13~112@ a13~106@)
                                                            (=>
                                                             %%location_label%%13
                                                             (= temp_13_0~3915@ temp_13_1~4024@)
                                                           ))
                                                           (=>
                                                            (= temp_13_0~3915@ temp_13_1~4024@)
                                                            (=>
                                                             (= temp_14_0~4197@ (Mul (Mul (Add (Mul (Mul d14~120@ d14~120@) (Mul d14~120@ c14~118@))
                                                                 (Mul (Add b14~116@ d14~120@) d14~120@)
                                                                ) (Mul (Mul (Mul b14~116@ b14~116@) (Add c14~118@ b14~116@)) (Mul (Mul b14~116@ d14~120@)
                                                                  (Sub d14~120@ d14~120@)
                                                                ))
                                                               ) (Mul (Mul (Mul (Mul c14~118@ 84) (Mul d14~120@ b14~116@)) (Add (Mul c14~118@ b14~116@)
                                                                  d14~120@
                                                                 )
                                                                ) (Add (Add (Mul a14~114@ b14~116@) (Mul a14~114@ b14~116@)) (Mul (Mul b14~116@ b14~116@)
                                                                  (Sub b14~116@ 23)
                                                             )))))
                                                             (=>
                                                              (= temp_14_1~4342@ (Mul (Mul (Add (Mul (Mul d14~120@ d14~120@) (Mul d14~120@ c14~118@))
                                                                  (Mul (Add b14~116@ d14~120@) d14~120@)
                                                                 ) (Mul (Mul (Mul b14~116@ b14~116@) (Add c14~118@ b14~116@)) (Mul (Mul b14~116@ d14~120@)
                                                                   (Sub d14~120@ d14~120@)
                                                                 ))
                                                                ) (Mul (Mul (Mul (Mul c14~118@ 84) (Mul d14~120@ b14~116@)) (Add (Mul c14~118@ b14~116@)
                                                                   d14~120@
                                                                  )
                                                                 ) (Add (Add (Mul a14~114@ b14~116@) (Mul a14~114@ b14~116@)) (Mul b14~116@ (Mul b14~116@
                                                                    (Sub b14~116@ 23)
                                                              ))))))
                                                              (=>
                                                               (= tmp%19@ (Sub b14~116@ 23))
                                                               (=>
                                                                (ens%main!nl_basics.lemma_mul_is_associative. b14~116@ b14~116@ tmp%19@)
                                                                (=>
                                                                 %%location_label%%14
                                                                 (= temp_14_0~4197@ temp_14_1~4342@)
 ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
 (get-info :version)
 (assert
  %%query%%
 )
 (set-option :rlimit 4294967295)
 (check-sat)
 (set-option :rlimit 0)
(pop)
