(set-option :auto_config false)
(set-option :smt.mbqi false)
(set-option :smt.case_split 3)
(set-option :smt.qi.eager_threshold 100.0)
(set-option :smt.delay_units true)
(set-option :smt.arith.solver 2)
(set-option :smt.arith.nl false)

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

;; Function-Decl main::nl_basics::eq_
(declare-fun main!nl_basics.eq_.? (Poly Poly) Bool)

;; Function-Decl main::nl_basics::add_
(declare-fun main!nl_basics.add_.? (Poly Poly) Int)

;; Function-Decl main::nl_basics::sub_
(declare-fun main!nl_basics.sub_.? (Poly Poly) Int)

;; Function-Decl main::nl_basics::mul_
(declare-fun main!nl_basics.mul_.? (Poly Poly) Int)

;; Function-Decl main::nl_basics::mod_
(declare-fun main!nl_basics.mod_.? (Poly Poly) Int)

;; Function-Specs main::nl_basics::lemma_mul_properties_auto_1
(declare-fun ens%main!nl_basics.lemma_mul_properties_auto_1. (Int) Bool)
(assert
 (forall ((no%param@ Int)) (!
   (= (ens%main!nl_basics.lemma_mul_properties_auto_1. no%param@) (and
     (forall ((x~14$ Poly) (y~16$ Poly)) (!
       (=>
        (and
         (has_type x~14$ INT)
         (has_type y~16$ INT)
        )
        (main!nl_basics.eq_.? (I (main!nl_basics.add_.? x~14$ y~16$)) (I (main!nl_basics.add_.?
           y~16$ x~14$
       ))))
       :pattern ((main!nl_basics.add_.? x~14$ y~16$))
       :pattern ((main!nl_basics.add_.? y~16$ x~14$))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_0
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_0
     ))
     (forall ((x~45$ Poly) (y~47$ Poly)) (!
       (=>
        (and
         (has_type x~45$ INT)
         (has_type y~47$ INT)
        )
        (main!nl_basics.eq_.? (I (main!nl_basics.mul_.? x~45$ y~47$)) (I (main!nl_basics.mul_.?
           y~47$ x~45$
       ))))
       :pattern ((main!nl_basics.mul_.? x~45$ y~47$))
       :pattern ((main!nl_basics.mul_.? y~47$ x~45$))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_1
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_1
     ))
     (forall ((x~76$ Poly) (y~78$ Poly) (z~80$ Poly)) (!
       (=>
        (and
         (has_type x~76$ INT)
         (has_type y~78$ INT)
         (has_type z~80$ INT)
        )
        (main!nl_basics.eq_.? (I (main!nl_basics.mul_.? x~76$ (I (main!nl_basics.mul_.? y~78$
             z~80$
          )))
         ) (I (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? x~76$ y~78$)) z~80$))
       ))
       :pattern ((main!nl_basics.mul_.? x~76$ (I (main!nl_basics.mul_.? y~78$ z~80$))))
       :pattern ((main!nl_basics.mul_.? (I (main!nl_basics.mul_.? x~76$ y~78$)) z~80$))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_2
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_2
     ))
     (forall ((x~121$ Poly) (y~123$ Poly) (z~125$ Poly)) (!
       (=>
        (and
         (has_type x~121$ INT)
         (has_type y~123$ INT)
         (has_type z~125$ INT)
        )
        (main!nl_basics.eq_.? (I (main!nl_basics.mul_.? x~121$ (I (main!nl_basics.add_.? y~123$
             z~125$
          )))
         ) (I (main!nl_basics.add_.? (I (main!nl_basics.mul_.? x~121$ y~123$)) (I (main!nl_basics.mul_.?
             x~121$ z~125$
       ))))))
       :pattern ((main!nl_basics.mul_.? x~121$ (I (main!nl_basics.add_.? y~123$ z~125$))))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_3
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_3
     ))
     (forall ((x~171$ Poly) (y~173$ Poly) (z~175$ Poly)) (!
       (=>
        (and
         (has_type x~171$ INT)
         (has_type y~173$ INT)
         (has_type z~175$ INT)
        )
        (main!nl_basics.eq_.? (I (main!nl_basics.mul_.? (I (main!nl_basics.add_.? x~171$ y~173$))
           z~175$
          )
         ) (I (main!nl_basics.add_.? (I (main!nl_basics.mul_.? x~171$ z~175$)) (I (main!nl_basics.mul_.?
             y~173$ z~175$
       ))))))
       :pattern ((main!nl_basics.mul_.? (I (main!nl_basics.add_.? x~171$ y~173$)) z~175$))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_4
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_4
     ))
     (forall ((x~221$ Poly) (y~223$ Poly) (z~225$ Poly)) (!
       (=>
        (and
         (has_type x~221$ INT)
         (has_type y~223$ INT)
         (has_type z~225$ INT)
        )
        (main!nl_basics.eq_.? (I (main!nl_basics.mul_.? (I (main!nl_basics.sub_.? y~223$ z~225$))
           x~221$
          )
         ) (I (main!nl_basics.sub_.? (I (main!nl_basics.mul_.? y~223$ x~221$)) (I (main!nl_basics.mul_.?
             z~225$ x~221$
       ))))))
       :pattern ((main!nl_basics.mul_.? (I (main!nl_basics.sub_.? y~223$ z~225$)) x~221$))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_5
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_5
     ))
     (forall ((x~271$ Poly) (y~273$ Poly) (z~275$ Poly)) (!
       (=>
        (and
         (has_type x~271$ INT)
         (has_type y~273$ INT)
         (has_type z~275$ INT)
        )
        (main!nl_basics.eq_.? (I (main!nl_basics.mul_.? (I (main!nl_basics.sub_.? x~271$ y~273$))
           z~275$
          )
         ) (I (main!nl_basics.sub_.? (I (main!nl_basics.mul_.? x~271$ z~275$)) (I (main!nl_basics.mul_.?
             y~273$ z~275$
       ))))))
       :pattern ((main!nl_basics.mul_.? (I (main!nl_basics.sub_.? x~271$ y~273$)) z~275$))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_6
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_6
     ))
     (forall ((x~321$ Poly) (y~323$ Poly) (m~325$ Poly)) (!
       (=>
        (and
         (has_type x~321$ INT)
         (has_type y~323$ INT)
         (has_type m~325$ INT)
        )
        (main!nl_basics.eq_.? (I (main!nl_basics.mod_.? (I (main!nl_basics.mod_.? (I (main!nl_basics.mul_.?
               x~321$ y~323$
              )
             ) m~325$
            )
           ) m~325$
          )
         ) (I (main!nl_basics.mod_.? (I (main!nl_basics.mul_.? (I (main!nl_basics.mod_.? x~321$
               m~325$
              )
             ) (I (main!nl_basics.mod_.? y~323$ m~325$))
            )
           ) m~325$
       ))))
       :pattern ((main!nl_basics.mod_.? (I (main!nl_basics.mod_.? (I (main!nl_basics.mul_.? x~321$
             y~323$
            )
           ) m~325$
          )
         ) m~325$
       ))
       :pattern ((main!nl_basics.mul_.? (I (main!nl_basics.mod_.? x~321$ m~325$)) (I (main!nl_basics.mod_.?
           y~323$ m~325$
       ))))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_7
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_7
     ))
     (forall ((x~381$ Poly) (y~383$ Poly) (m~385$ Poly)) (!
       (=>
        (and
         (has_type x~381$ INT)
         (has_type y~383$ INT)
         (has_type m~385$ INT)
        )
        (main!nl_basics.eq_.? (I (main!nl_basics.mod_.? (I (main!nl_basics.mod_.? (I (main!nl_basics.mul_.?
               x~381$ y~383$
              )
             ) m~385$
            )
           ) m~385$
          )
         ) (I (main!nl_basics.mod_.? (I (main!nl_basics.mul_.? x~381$ (I (main!nl_basics.mod_.?
               y~383$ m~385$
            )))
           ) m~385$
       ))))
       :pattern ((main!nl_basics.mul_.? x~381$ (I (main!nl_basics.mod_.? y~383$ m~385$))))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_8
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_8
     ))
     (forall ((x~436$ Poly) (y~438$ Poly) (m~440$ Poly)) (!
       (=>
        (and
         (has_type x~436$ INT)
         (has_type y~438$ INT)
         (has_type m~440$ INT)
        )
        (main!nl_basics.eq_.? (I (main!nl_basics.mod_.? (I (main!nl_basics.mod_.? (I (main!nl_basics.mul_.?
               x~436$ y~438$
              )
             ) m~440$
            )
           ) m~440$
          )
         ) (I (main!nl_basics.mod_.? (I (main!nl_basics.mul_.? y~438$ (I (main!nl_basics.mod_.?
               x~436$ m~440$
            )))
           ) m~440$
       ))))
       :pattern ((main!nl_basics.mul_.? y~438$ (I (main!nl_basics.mod_.? x~436$ m~440$))))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_9
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_9
     ))
     (forall ((x~491$ Poly) (y~493$ Poly) (m~495$ Poly)) (!
       (=>
        (and
         (has_type x~491$ INT)
         (has_type y~493$ INT)
         (has_type m~495$ INT)
        )
        (main!nl_basics.eq_.? (I (main!nl_basics.mod_.? x~491$ m~495$)) (I (main!nl_basics.mod_.?
           (I (main!nl_basics.add_.? x~491$ (I (main!nl_basics.mul_.? y~493$ m~495$)))) m~495$
       ))))
       :pattern ((main!nl_basics.add_.? x~491$ (I (main!nl_basics.mul_.? y~493$ m~495$))))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_10
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_10
     ))
     (forall ((x~536$ Poly) (y~538$ Poly) (m~540$ Poly)) (!
       (=>
        (and
         (has_type x~536$ INT)
         (has_type y~538$ INT)
         (has_type m~540$ INT)
        )
        (main!nl_basics.eq_.? (I (main!nl_basics.mod_.? x~536$ m~540$)) (I (main!nl_basics.mod_.?
           (I (main!nl_basics.add_.? (I (main!nl_basics.mul_.? y~538$ m~540$)) x~536$)) m~540$
       ))))
       :pattern ((main!nl_basics.add_.? (I (main!nl_basics.mul_.? y~538$ m~540$)) x~536$))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_11
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_11
     ))
     (forall ((x~581$ Poly) (y~583$ Poly) (m~585$ Poly)) (!
       (=>
        (and
         (has_type x~581$ INT)
         (has_type y~583$ INT)
         (has_type m~585$ INT)
        )
        (main!nl_basics.eq_.? (I (main!nl_basics.mod_.? x~581$ m~585$)) (I (main!nl_basics.mod_.?
           (I (main!nl_basics.sub_.? x~581$ (I (main!nl_basics.mul_.? y~583$ m~585$)))) m~585$
       ))))
       :pattern ((main!nl_basics.sub_.? x~581$ (I (main!nl_basics.mul_.? y~583$ m~585$))))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_12
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_12
     ))
     (forall ((x~626$ Poly) (y~628$ Poly) (m~630$ Poly)) (!
       (=>
        (and
         (has_type x~626$ INT)
         (has_type y~628$ INT)
         (has_type m~630$ INT)
        )
        (main!nl_basics.eq_.? (I (main!nl_basics.mod_.? (I (main!nl_basics.add_.? x~626$ y~628$))
           m~630$
          )
         ) (I (main!nl_basics.mod_.? (I (main!nl_basics.add_.? (I (main!nl_basics.mod_.? x~626$
               m~630$
              )
             ) (I (main!nl_basics.mod_.? y~628$ m~630$))
            )
           ) m~630$
       ))))
       :pattern ((main!nl_basics.add_.? (I (main!nl_basics.mod_.? x~626$ m~630$)) (I (main!nl_basics.mod_.?
           y~628$ m~630$
       ))))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_13
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_13
     ))
     (forall ((x~681$ Poly) (y~683$ Poly) (m~685$ Poly)) (!
       (=>
        (and
         (has_type x~681$ INT)
         (has_type y~683$ INT)
         (has_type m~685$ INT)
        )
        (main!nl_basics.eq_.? (I (main!nl_basics.mod_.? (I (main!nl_basics.add_.? x~681$ y~683$))
           m~685$
          )
         ) (I (main!nl_basics.mod_.? (I (main!nl_basics.add_.? x~681$ (I (main!nl_basics.mod_.?
               y~683$ m~685$
            )))
           ) m~685$
       ))))
       :pattern ((main!nl_basics.add_.? x~681$ (I (main!nl_basics.mod_.? y~683$ m~685$))))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_14
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_14
     ))
     (forall ((x~731$ Poly) (y~733$ Poly) (m~735$ Poly)) (!
       (=>
        (and
         (has_type x~731$ INT)
         (has_type y~733$ INT)
         (has_type m~735$ INT)
        )
        (main!nl_basics.eq_.? (I (main!nl_basics.mod_.? (I (main!nl_basics.add_.? x~731$ y~733$))
           m~735$
          )
         ) (I (main!nl_basics.mod_.? (I (main!nl_basics.add_.? (I (main!nl_basics.mod_.? x~731$
               m~735$
              )
             ) y~733$
            )
           ) m~735$
       ))))
       :pattern ((main!nl_basics.add_.? (I (main!nl_basics.mod_.? x~731$ m~735$)) y~733$))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_15
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_15
     ))
     (forall ((x~781$ Poly) (y~783$ Poly) (m~785$ Poly)) (!
       (=>
        (and
         (has_type x~781$ INT)
         (has_type y~783$ INT)
         (has_type m~785$ INT)
        )
        (main!nl_basics.eq_.? (I (main!nl_basics.mod_.? (I (main!nl_basics.sub_.? x~781$ y~783$))
           m~785$
          )
         ) (I (main!nl_basics.mod_.? (I (main!nl_basics.sub_.? (I (main!nl_basics.mod_.? x~781$
               m~785$
              )
             ) (I (main!nl_basics.mod_.? y~783$ m~785$))
            )
           ) m~785$
       ))))
       :pattern ((main!nl_basics.sub_.? (I (main!nl_basics.mod_.? x~781$ m~785$)) (I (main!nl_basics.mod_.?
           y~783$ m~785$
       ))))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_16
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_16
     ))
     (forall ((x~836$ Poly) (y~838$ Poly) (m~840$ Poly)) (!
       (=>
        (and
         (has_type x~836$ INT)
         (has_type y~838$ INT)
         (has_type m~840$ INT)
        )
        (main!nl_basics.eq_.? (I (main!nl_basics.mod_.? (I (main!nl_basics.sub_.? x~836$ y~838$))
           m~840$
          )
         ) (I (main!nl_basics.mod_.? (I (main!nl_basics.sub_.? x~836$ (I (main!nl_basics.mod_.?
               y~838$ m~840$
            )))
           ) m~840$
       ))))
       :pattern ((main!nl_basics.sub_.? x~836$ (I (main!nl_basics.mod_.? y~838$ m~840$))))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_17
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_17
     ))
     (forall ((x~886$ Poly) (y~888$ Poly) (m~890$ Poly)) (!
       (=>
        (and
         (has_type x~886$ INT)
         (has_type y~888$ INT)
         (has_type m~890$ INT)
        )
        (main!nl_basics.eq_.? (I (main!nl_basics.mod_.? (I (main!nl_basics.sub_.? x~886$ y~888$))
           m~890$
          )
         ) (I (main!nl_basics.mod_.? (I (main!nl_basics.sub_.? (I (main!nl_basics.mod_.? x~886$
               m~890$
              )
             ) y~888$
            )
           ) m~890$
       ))))
       :pattern ((main!nl_basics.sub_.? (I (main!nl_basics.mod_.? x~886$ m~890$)) y~888$))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_18
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_18
     ))
     (forall ((x~936$ Poly)) (!
       (=>
        (has_type x~936$ INT)
        (main!nl_basics.eq_.? x~936$ x~936$)
       )
       :pattern ((main!nl_basics.eq_.? x~936$ x~936$))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_19
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_19
     ))
     (forall ((x~953$ Poly) (y~955$ Poly)) (!
       (=>
        (and
         (has_type x~953$ INT)
         (has_type y~955$ INT)
        )
        (=>
         (main!nl_basics.eq_.? x~953$ y~955$)
         (main!nl_basics.eq_.? y~955$ x~953$)
       ))
       :pattern ((main!nl_basics.eq_.? x~953$ y~955$))
       :pattern ((main!nl_basics.eq_.? y~955$ x~953$))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_20
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_20
     ))
     (forall ((x~986$ Poly) (y~988$ Poly) (z~990$ Poly)) (!
       (=>
        (and
         (has_type x~986$ INT)
         (has_type y~988$ INT)
         (has_type z~990$ INT)
        )
        (=>
         (and
          (main!nl_basics.eq_.? x~986$ y~988$)
          (main!nl_basics.eq_.? y~988$ z~990$)
         )
         (main!nl_basics.eq_.? x~986$ z~990$)
       ))
       :pattern ((main!nl_basics.eq_.? x~986$ y~988$) (main!nl_basics.eq_.? y~988$ z~990$))
       :pattern ((main!nl_basics.eq_.? x~986$ y~988$) (main!nl_basics.eq_.? x~986$ z~990$))
       :pattern ((main!nl_basics.eq_.? x~986$ y~988$) (main!nl_basics.eq_.? x~986$ z~990$))
       :pattern ((main!nl_basics.eq_.? y~988$ z~990$) (main!nl_basics.eq_.? x~986$ z~990$))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_21
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_21
     ))
     (forall ((x0~1031$ Poly) (y0~1033$ Poly) (x1~1035$ Poly) (y1~1037$ Poly)) (!
       (=>
        (and
         (has_type x0~1031$ INT)
         (has_type y0~1033$ INT)
         (has_type x1~1035$ INT)
         (has_type y1~1037$ INT)
        )
        (=>
         (and
          (main!nl_basics.eq_.? x0~1031$ x1~1035$)
          (main!nl_basics.eq_.? y0~1033$ y1~1037$)
         )
         (main!nl_basics.eq_.? (I (main!nl_basics.add_.? x0~1031$ y0~1033$)) (I (main!nl_basics.add_.?
            x1~1035$ y1~1037$
       )))))
       :pattern ((main!nl_basics.eq_.? (I (main!nl_basics.add_.? x0~1031$ y0~1033$)) (I (main!nl_basics.add_.?
           x1~1035$ y1~1037$
       ))))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_22
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_22
     ))
     (forall ((x0~1090$ Poly) (y0~1092$ Poly) (x1~1094$ Poly) (y1~1096$ Poly)) (!
       (=>
        (and
         (has_type x0~1090$ INT)
         (has_type y0~1092$ INT)
         (has_type x1~1094$ INT)
         (has_type y1~1096$ INT)
        )
        (=>
         (and
          (main!nl_basics.eq_.? x0~1090$ x1~1094$)
          (main!nl_basics.eq_.? y0~1092$ y1~1096$)
         )
         (main!nl_basics.eq_.? (I (main!nl_basics.sub_.? x0~1090$ y0~1092$)) (I (main!nl_basics.sub_.?
            x1~1094$ y1~1096$
       )))))
       :pattern ((main!nl_basics.eq_.? (I (main!nl_basics.sub_.? x0~1090$ y0~1092$)) (I (main!nl_basics.sub_.?
           x1~1094$ y1~1096$
       ))))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_23
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_23
     ))
     (forall ((x0~1149$ Poly) (y0~1151$ Poly) (x1~1153$ Poly) (y1~1155$ Poly)) (!
       (=>
        (and
         (has_type x0~1149$ INT)
         (has_type y0~1151$ INT)
         (has_type x1~1153$ INT)
         (has_type y1~1155$ INT)
        )
        (=>
         (and
          (main!nl_basics.eq_.? x0~1149$ x1~1153$)
          (main!nl_basics.eq_.? y0~1151$ y1~1155$)
         )
         (main!nl_basics.eq_.? (I (main!nl_basics.mul_.? x0~1149$ y0~1151$)) (I (main!nl_basics.mul_.?
            x1~1153$ y1~1155$
       )))))
       :pattern ((main!nl_basics.eq_.? (I (main!nl_basics.mul_.? x0~1149$ y0~1151$)) (I (main!nl_basics.mul_.?
           x1~1153$ y1~1155$
       ))))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_24
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_24
     ))
     (forall ((x0~1208$ Poly) (y0~1210$ Poly) (x1~1212$ Poly) (y1~1214$ Poly)) (!
       (=>
        (and
         (has_type x0~1208$ INT)
         (has_type y0~1210$ INT)
         (has_type x1~1212$ INT)
         (has_type y1~1214$ INT)
        )
        (=>
         (and
          (main!nl_basics.eq_.? x0~1208$ x1~1212$)
          (main!nl_basics.eq_.? y0~1210$ y1~1214$)
         )
         (main!nl_basics.eq_.? (I (main!nl_basics.mod_.? x0~1208$ y0~1210$)) (I (main!nl_basics.mod_.?
            x1~1212$ y1~1214$
       )))))
       :pattern ((main!nl_basics.eq_.? (I (main!nl_basics.mod_.? x0~1208$ y0~1210$)) (I (main!nl_basics.mod_.?
           x1~1212$ y1~1214$
       ))))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_25
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_25
   ))))
   :pattern ((ens%main!nl_basics.lemma_mul_properties_auto_1. no%param@))
   :qid internal_ens__main!nl_basics.lemma_mul_properties_auto_1._definition
   :skolemid skolem_internal_ens__main!nl_basics.lemma_mul_properties_auto_1._definition
)))

;; Function-Def main::auto_0
;; mariposa_data/uf//13597416436139611618/nlqi_verus/src/main.rs:7:1: 7:60 (#0)
(push)
 (declare-const a~2@ Int)
 (declare-const b~4@ Int)
 (declare-const c~6@ Int)
 (declare-const d~8@ Int)
 (declare-const m~10@ Int)
 (declare-const temp_0_0~35@ Int)
 (declare-const temp_0_1~60@ Int)
 (declare-const temp_1_0~102@ Int)
 (declare-const temp_1_1~122@ Int)
 (declare-const temp_2_0~164@ Int)
 (declare-const temp_2_1~184@ Int)
 (declare-const temp_3_0~226@ Int)
 (declare-const temp_3_1~246@ Int)
 (declare-const temp_4_0~305@ Int)
 (declare-const temp_4_1~342@ Int)
 (declare-const temp_5_0~396@ Int)
 (declare-const temp_5_1~428@ Int)
 (declare-const temp_6_0~470@ Int)
 (declare-const temp_6_1~490@ Int)
 (declare-const temp_7_0~537@ Int)
 (declare-const temp_7_1~587@ Int)
 (declare-const temp_8_0~629@ Int)
 (declare-const temp_8_1~659@ Int)
 (declare-const temp_9_0~701@ Int)
 (declare-const temp_9_1~721@ Int)
 (declare-const temp_10_0~763@ Int)
 (declare-const temp_10_1~783@ Int)
 (declare-const temp_11_0~830@ Int)
 (declare-const temp_11_1~880@ Int)
 (declare-const temp_12_0~927@ Int)
 (declare-const temp_12_1~952@ Int)
 (declare-const temp_13_0~994@ Int)
 (declare-const temp_13_1~1014@ Int)
 (declare-const temp_14_0~1061@ Int)
 (declare-const temp_14_1~1116@ Int)
 (declare-const temp_15_0~1180@ Int)
 (declare-const temp_15_1~1269@ Int)
 (declare-const temp_16_0~1323@ Int)
 (declare-const temp_16_1~1355@ Int)
 (declare-const temp_17_0~1402@ Int)
 (declare-const temp_17_1~1427@ Int)
 (declare-const temp_18_0~1469@ Int)
 (declare-const temp_18_1~1489@ Int)
 (declare-const temp_19_0~1536@ Int)
 (declare-const temp_19_1~1561@ Int)
 (declare-const temp_20_0~1603@ Int)
 (declare-const temp_20_1~1623@ Int)
 (declare-const temp_21_0~1670@ Int)
 (declare-const temp_21_1~1720@ Int)
 (declare-const temp_22_0~1762@ Int)
 (declare-const temp_22_1~1782@ Int)
 (declare-const temp_23_0~1841@ Int)
 (declare-const temp_23_1~1878@ Int)
 (declare-const temp_24_0~1920@ Int)
 (declare-const temp_24_1~1940@ Int)
 (declare-const temp_25_0~1982@ Int)
 (declare-const temp_25_1~2002@ Int)
 (declare-const temp_26_0~2051@ Int)
 (declare-const temp_26_1~2078@ Int)
 (declare-const temp_27_0~2130@ Int)
 (declare-const temp_27_1~2160@ Int)
 (declare-const temp_28_0~2212@ Int)
 (declare-const temp_28_1~2277@ Int)
 (declare-const temp_29_0~2319@ Int)
 (declare-const temp_29_1~2339@ Int)
 (declare-const temp_30_0~2381@ Int)
 (declare-const temp_30_1~2401@ Int)
 (declare-const temp_31_0~2448@ Int)
 (declare-const temp_31_1~2498@ Int)
 (declare-const temp_32_0~2540@ Int)
 (declare-const temp_32_1~2560@ Int)
 (declare-const temp_33_0~2607@ Int)
 (declare-const temp_33_1~2632@ Int)
 (declare-const temp_34_0~2674@ Int)
 (declare-const temp_34_1~2694@ Int)
 (declare-const temp_35_0~2753@ Int)
 (declare-const temp_35_1~2790@ Int)
 (declare-const temp_36_0~2837@ Int)
 (declare-const temp_36_1~2862@ Int)
 (declare-const temp_37_0~2909@ Int)
 (declare-const temp_37_1~2964@ Int)
 (declare-const temp_38_0~3006@ Int)
 (declare-const temp_38_1~3026@ Int)
 (declare-const temp_39_0~3068@ Int)
 (declare-const temp_39_1~3088@ Int)
 (declare-const temp_40_0~3130@ Int)
 (declare-const temp_40_1~3150@ Int)
 (declare-const temp_41_0~3192@ Int)
 (declare-const temp_41_1~3212@ Int)
 (declare-const temp_42_0~3254@ Int)
 (declare-const temp_42_1~3284@ Int)
 (declare-const temp_43_0~3326@ Int)
 (declare-const temp_43_1~3346@ Int)
 (declare-const temp_44_0~3393@ Int)
 (declare-const temp_44_1~3433@ Int)
 (declare-const temp_45_0~3475@ Int)
 (declare-const temp_45_1~3495@ Int)
 (declare-const temp_46_0~3552@ Int)
 (declare-const temp_46_1~3587@ Int)
 (declare-const temp_47_0~3629@ Int)
 (declare-const temp_47_1~3649@ Int)
 (declare-const temp_48_0~3701@ Int)
 (declare-const temp_48_1~3731@ Int)
 (declare-const temp_49_0~3783@ Int)
 (declare-const temp_49_1~3813@ Int)
 (declare-const temp_50_0~3860@ Int)
 (declare-const temp_50_1~3895@ Int)
 (declare-const temp_51_0~3947@ Int)
 (declare-const temp_51_1~3977@ Int)
 (declare-const temp_52_0~4031@ Int)
 (declare-const temp_52_1~4063@ Int)
 (declare-const temp_53_0~4117@ Int)
 (declare-const temp_53_1~4149@ Int)
 (declare-const temp_54_0~4191@ Int)
 (declare-const temp_54_1~4221@ Int)
 (declare-const temp_55_0~4263@ Int)
 (declare-const temp_55_1~4283@ Int)
 (declare-const temp_56_0~4337@ Int)
 (declare-const temp_56_1~4369@ Int)
 (declare-const temp_57_0~4411@ Int)
 (declare-const temp_57_1~4431@ Int)
 (declare-const temp_58_0~4478@ Int)
 (declare-const temp_58_1~4528@ Int)
 (declare-const temp_59_0~4575@ Int)
 (declare-const temp_59_1~4600@ Int)
 (declare-const temp_60_0~4652@ Int)
 (declare-const temp_60_1~4707@ Int)
 (declare-const temp_61_0~4761@ Int)
 (declare-const temp_61_1~4793@ Int)
 (declare-const temp_62_0~4830@ Int)
 (declare-const temp_62_1~4845@ Int)
 (declare-const temp_63_0~4892@ Int)
 (declare-const temp_63_1~4917@ Int)
 (declare-const temp_64_0~4964@ Int)
 (declare-const temp_64_1~5024@ Int)
 (declare-const temp_65_0~5066@ Int)
 (declare-const temp_65_1~5086@ Int)
 (declare-const temp_66_0~5128@ Int)
 (declare-const temp_66_1~5148@ Int)
 (declare-const temp_67_0~5195@ Int)
 (declare-const temp_67_1~5250@ Int)
 (declare-const temp_68_0~5297@ Int)
 (declare-const temp_68_1~5322@ Int)
 (declare-const temp_69_0~5364@ Int)
 (declare-const temp_69_1~5394@ Int)
 (declare-const temp_70_0~5436@ Int)
 (declare-const temp_70_1~5456@ Int)
 (declare-const temp_71_0~5498@ Int)
 (declare-const temp_71_1~5518@ Int)
 (declare-const temp_72_0~5575@ Int)
 (declare-const temp_72_1~5610@ Int)
 (declare-const temp_73_0~5652@ Int)
 (declare-const temp_73_1~5672@ Int)
 (declare-const temp_74_0~5724@ Int)
 (declare-const temp_74_1~5754@ Int)
 (declare-const temp_75_0~5801@ Int)
 (declare-const temp_75_1~5856@ Int)
 (declare-const temp_76_0~5908@ Int)
 (declare-const temp_76_1~5938@ Int)
 (declare-const temp_77_0~5980@ Int)
 (declare-const temp_77_1~6000@ Int)
 (declare-const temp_78_0~6042@ Int)
 (declare-const temp_78_1~6062@ Int)
 (declare-const temp_79_0~6114@ Int)
 (declare-const temp_79_1~6159@ Int)
 (declare-const temp_80_0~6206@ Int)
 (declare-const temp_80_1~6261@ Int)
 (declare-const temp_81_0~6303@ Int)
 (declare-const temp_81_1~6323@ Int)
 (declare-const temp_82_0~6365@ Int)
 (declare-const temp_82_1~6385@ Int)
 (declare-const temp_83_0~6427@ Int)
 (declare-const temp_83_1~6447@ Int)
 (declare-const temp_84_0~6489@ Int)
 (declare-const temp_84_1~6509@ Int)
 (declare-const temp_85_0~6556@ Int)
 (declare-const temp_85_1~6581@ Int)
 (declare-const temp_86_0~6623@ Int)
 (declare-const temp_86_1~6643@ Int)
 (declare-const temp_87_0~6685@ Int)
 (declare-const temp_87_1~6705@ Int)
 (declare-const temp_88_0~6747@ Int)
 (declare-const temp_88_1~6767@ Int)
 (declare-const temp_89_0~6819@ Int)
 (declare-const temp_89_1~6849@ Int)
 (declare-const temp_90_0~6896@ Int)
 (declare-const temp_90_1~6951@ Int)
 (declare-const temp_91_0~6993@ Int)
 (declare-const temp_91_1~7013@ Int)
 (declare-const temp_92_0~7065@ Int)
 (declare-const temp_92_1~7125@ Int)
 (declare-const temp_93_0~7172@ Int)
 (declare-const temp_93_1~7227@ Int)
 (declare-const temp_94_0~7269@ Int)
 (declare-const temp_94_1~7289@ Int)
 (declare-const temp_95_0~7336@ Int)
 (declare-const temp_95_1~7361@ Int)
 (declare-const temp_96_0~7415@ Int)
 (declare-const temp_96_1~7447@ Int)
 (declare-const temp_97_0~7494@ Int)
 (declare-const temp_97_1~7519@ Int)
 (declare-const temp_98_0~7566@ Int)
 (declare-const temp_98_1~7621@ Int)
 (declare-const temp_99_0~7673@ Int)
 (declare-const temp_99_1~7733@ Int)
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
 ;; assertion failed
 (declare-const %%location_label%%17 Bool)
 ;; assertion failed
 (declare-const %%location_label%%18 Bool)
 ;; assertion failed
 (declare-const %%location_label%%19 Bool)
 ;; assertion failed
 (declare-const %%location_label%%20 Bool)
 ;; assertion failed
 (declare-const %%location_label%%21 Bool)
 ;; assertion failed
 (declare-const %%location_label%%22 Bool)
 ;; assertion failed
 (declare-const %%location_label%%23 Bool)
 ;; assertion failed
 (declare-const %%location_label%%24 Bool)
 ;; assertion failed
 (declare-const %%location_label%%25 Bool)
 ;; assertion failed
 (declare-const %%location_label%%26 Bool)
 ;; assertion failed
 (declare-const %%location_label%%27 Bool)
 ;; assertion failed
 (declare-const %%location_label%%28 Bool)
 ;; assertion failed
 (declare-const %%location_label%%29 Bool)
 ;; assertion failed
 (declare-const %%location_label%%30 Bool)
 ;; assertion failed
 (declare-const %%location_label%%31 Bool)
 ;; assertion failed
 (declare-const %%location_label%%32 Bool)
 ;; assertion failed
 (declare-const %%location_label%%33 Bool)
 ;; assertion failed
 (declare-const %%location_label%%34 Bool)
 ;; assertion failed
 (declare-const %%location_label%%35 Bool)
 ;; assertion failed
 (declare-const %%location_label%%36 Bool)
 ;; assertion failed
 (declare-const %%location_label%%37 Bool)
 ;; assertion failed
 (declare-const %%location_label%%38 Bool)
 ;; assertion failed
 (declare-const %%location_label%%39 Bool)
 ;; assertion failed
 (declare-const %%location_label%%40 Bool)
 ;; assertion failed
 (declare-const %%location_label%%41 Bool)
 ;; assertion failed
 (declare-const %%location_label%%42 Bool)
 ;; assertion failed
 (declare-const %%location_label%%43 Bool)
 ;; assertion failed
 (declare-const %%location_label%%44 Bool)
 ;; assertion failed
 (declare-const %%location_label%%45 Bool)
 ;; assertion failed
 (declare-const %%location_label%%46 Bool)
 ;; assertion failed
 (declare-const %%location_label%%47 Bool)
 ;; assertion failed
 (declare-const %%location_label%%48 Bool)
 ;; assertion failed
 (declare-const %%location_label%%49 Bool)
 ;; assertion failed
 (declare-const %%location_label%%50 Bool)
 ;; assertion failed
 (declare-const %%location_label%%51 Bool)
 ;; assertion failed
 (declare-const %%location_label%%52 Bool)
 ;; assertion failed
 (declare-const %%location_label%%53 Bool)
 ;; assertion failed
 (declare-const %%location_label%%54 Bool)
 ;; assertion failed
 (declare-const %%location_label%%55 Bool)
 ;; assertion failed
 (declare-const %%location_label%%56 Bool)
 ;; assertion failed
 (declare-const %%location_label%%57 Bool)
 ;; assertion failed
 (declare-const %%location_label%%58 Bool)
 ;; assertion failed
 (declare-const %%location_label%%59 Bool)
 ;; assertion failed
 (declare-const %%location_label%%60 Bool)
 ;; assertion failed
 (declare-const %%location_label%%61 Bool)
 ;; assertion failed
 (declare-const %%location_label%%62 Bool)
 ;; assertion failed
 (declare-const %%location_label%%63 Bool)
 ;; assertion failed
 (declare-const %%location_label%%64 Bool)
 ;; assertion failed
 (declare-const %%location_label%%65 Bool)
 ;; assertion failed
 (declare-const %%location_label%%66 Bool)
 ;; assertion failed
 (declare-const %%location_label%%67 Bool)
 ;; assertion failed
 (declare-const %%location_label%%68 Bool)
 ;; assertion failed
 (declare-const %%location_label%%69 Bool)
 ;; assertion failed
 (declare-const %%location_label%%70 Bool)
 ;; assertion failed
 (declare-const %%location_label%%71 Bool)
 ;; assertion failed
 (declare-const %%location_label%%72 Bool)
 ;; assertion failed
 (declare-const %%location_label%%73 Bool)
 ;; assertion failed
 (declare-const %%location_label%%74 Bool)
 ;; assertion failed
 (declare-const %%location_label%%75 Bool)
 ;; assertion failed
 (declare-const %%location_label%%76 Bool)
 ;; assertion failed
 (declare-const %%location_label%%77 Bool)
 ;; assertion failed
 (declare-const %%location_label%%78 Bool)
 ;; assertion failed
 (declare-const %%location_label%%79 Bool)
 ;; assertion failed
 (declare-const %%location_label%%80 Bool)
 ;; assertion failed
 (declare-const %%location_label%%81 Bool)
 ;; assertion failed
 (declare-const %%location_label%%82 Bool)
 ;; assertion failed
 (declare-const %%location_label%%83 Bool)
 ;; assertion failed
 (declare-const %%location_label%%84 Bool)
 ;; assertion failed
 (declare-const %%location_label%%85 Bool)
 ;; assertion failed
 (declare-const %%location_label%%86 Bool)
 ;; assertion failed
 (declare-const %%location_label%%87 Bool)
 ;; assertion failed
 (declare-const %%location_label%%88 Bool)
 ;; assertion failed
 (declare-const %%location_label%%89 Bool)
 ;; assertion failed
 (declare-const %%location_label%%90 Bool)
 ;; assertion failed
 (declare-const %%location_label%%91 Bool)
 ;; assertion failed
 (declare-const %%location_label%%92 Bool)
 ;; assertion failed
 (declare-const %%location_label%%93 Bool)
 ;; assertion failed
 (declare-const %%location_label%%94 Bool)
 ;; assertion failed
 (declare-const %%location_label%%95 Bool)
 ;; assertion failed
 (declare-const %%location_label%%96 Bool)
 ;; assertion failed
 (declare-const %%location_label%%97 Bool)
 ;; assertion failed
 (declare-const %%location_label%%98 Bool)
 ;; assertion failed
 (declare-const %%location_label%%99 Bool)
 (declare-const %%query%% Bool)
 (assert
  (=>
   %%query%%
   (not (=>
     (= temp_0_0~35@ (main!nl_basics.mod_.? (I (main!nl_basics.mul_.? (I (main!nl_basics.sub_.?
           (I c~6@) (I b~4@)
          )
         ) (I (main!nl_basics.mul_.? (I d~8@) (I b~4@)))
        )
       ) (I m~10@)
     ))
     (=>
      (= temp_0_1~60@ (main!nl_basics.mod_.? (I (main!nl_basics.mul_.? (I (main!nl_basics.mul_.?
            (I (main!nl_basics.sub_.? (I c~6@) (I b~4@))) (I d~8@)
           )
          ) (I b~4@)
         )
        ) (I m~10@)
      ))
      (and
       (=>
        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
        (=>
         %%location_label%%0
         (main!nl_basics.eq_.? (I temp_0_0~35@) (I temp_0_1~60@))
       ))
       (=>
        (main!nl_basics.eq_.? (I temp_0_0~35@) (I temp_0_1~60@))
        (=>
         (= temp_1_0~102@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I b~4@) (I c~6@)))
           (I (main!nl_basics.mul_.? (I a~2@) (I c~6@)))
         ))
         (=>
          (= temp_1_1~122@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I a~2@) (I c~6@)))
            (I (main!nl_basics.mul_.? (I b~4@) (I c~6@)))
          ))
          (and
           (=>
            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
            (=>
             %%location_label%%1
             (main!nl_basics.eq_.? (I temp_1_0~102@) (I temp_1_1~122@))
           ))
           (=>
            (main!nl_basics.eq_.? (I temp_1_0~102@) (I temp_1_1~122@))
            (=>
             (= temp_2_0~164@ (main!nl_basics.sub_.? (I (main!nl_basics.mul_.? (I a~2@) (I b~4@)))
               (I (main!nl_basics.sub_.? (I d~8@) (I d~8@)))
             ))
             (=>
              (= temp_2_1~184@ (main!nl_basics.sub_.? (I (main!nl_basics.mul_.? (I b~4@) (I a~2@)))
                (I (main!nl_basics.sub_.? (I d~8@) (I d~8@)))
              ))
              (and
               (=>
                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                (=>
                 %%location_label%%2
                 (main!nl_basics.eq_.? (I temp_2_0~164@) (I temp_2_1~184@))
               ))
               (=>
                (main!nl_basics.eq_.? (I temp_2_0~164@) (I temp_2_1~184@))
                (=>
                 (= temp_3_0~226@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I c~6@) (I a~2@)))
                   (I (main!nl_basics.sub_.? (I b~4@) (I d~8@)))
                 ))
                 (=>
                  (= temp_3_1~246@ (main!nl_basics.mul_.? (I c~6@) (I (main!nl_basics.mul_.? (I a~2@) (
                       I (main!nl_basics.sub_.? (I b~4@) (I d~8@))
                  )))))
                  (and
                   (=>
                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                    (=>
                     %%location_label%%3
                     (main!nl_basics.eq_.? (I temp_3_0~226@) (I temp_3_1~246@))
                   ))
                   (=>
                    (main!nl_basics.eq_.? (I temp_3_0~226@) (I temp_3_1~246@))
                    (=>
                     (= temp_4_0~305@ (main!nl_basics.add_.? (I (main!nl_basics.mul_.? (I d~8@) (I c~6@)))
                       (I (main!nl_basics.mul_.? (I (main!nl_basics.mod_.? (I 90) (I m~10@))) (I b~4@)))
                     ))
                     (=>
                      (= temp_4_1~342@ (main!nl_basics.add_.? (I (main!nl_basics.mul_.? (I (main!nl_basics.mod_.?
                            (I 90) (I m~10@)
                           )
                          ) (I b~4@)
                         )
                        ) (I (main!nl_basics.mul_.? (I d~8@) (I c~6@)))
                      ))
                      (and
                       (=>
                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                        (=>
                         %%location_label%%4
                         (main!nl_basics.eq_.? (I temp_4_0~305@) (I temp_4_1~342@))
                       ))
                       (=>
                        (main!nl_basics.eq_.? (I temp_4_0~305@) (I temp_4_1~342@))
                        (=>
                         (= temp_5_0~396@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I c~6@) (I 38)))
                           (I (main!nl_basics.sub_.? (I a~2@) (I b~4@)))
                         ))
                         (=>
                          (= temp_5_1~428@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I 38) (I c~6@)))
                            (I (main!nl_basics.sub_.? (I a~2@) (I b~4@)))
                          ))
                          (and
                           (=>
                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                            (=>
                             %%location_label%%5
                             (main!nl_basics.eq_.? (I temp_5_0~396@) (I temp_5_1~428@))
                           ))
                           (=>
                            (main!nl_basics.eq_.? (I temp_5_0~396@) (I temp_5_1~428@))
                            (=>
                             (= temp_6_0~470@ (main!nl_basics.add_.? (I (main!nl_basics.mul_.? (I b~4@) (I d~8@)))
                               (I (main!nl_basics.mul_.? (I a~2@) (I b~4@)))
                             ))
                             (=>
                              (= temp_6_1~490@ (main!nl_basics.add_.? (I (main!nl_basics.mul_.? (I b~4@) (I d~8@)))
                                (I (main!nl_basics.mul_.? (I b~4@) (I a~2@)))
                              ))
                              (and
                               (=>
                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                (=>
                                 %%location_label%%6
                                 (main!nl_basics.eq_.? (I temp_6_0~470@) (I temp_6_1~490@))
                               ))
                               (=>
                                (main!nl_basics.eq_.? (I temp_6_0~470@) (I temp_6_1~490@))
                                (=>
                                 (= temp_7_0~537@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I b~4@) (I b~4@)))
                                   (I (main!nl_basics.mod_.? (I (main!nl_basics.mul_.? (I a~2@) (I c~6@))) (I m~10@)))
                                 ))
                                 (=>
                                  (= temp_7_1~587@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I b~4@) (I b~4@)))
                                    (I (main!nl_basics.mod_.? (I (main!nl_basics.add_.? (I (main!nl_basics.mul_.? (I a~2@)
                                          (I c~6@)
                                         )
                                        ) (I (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I d~8@)
                                              (I b~4@)
                                             )
                                            ) (I (main!nl_basics.mul_.? (I b~4@) (I b~4@)))
                                           )
                                          ) (I m~10@)
                                       )))
                                      ) (I m~10@)
                                  ))))
                                  (and
                                   (=>
                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                    (=>
                                     %%location_label%%7
                                     (main!nl_basics.eq_.? (I temp_7_0~537@) (I temp_7_1~587@))
                                   ))
                                   (=>
                                    (main!nl_basics.eq_.? (I temp_7_0~537@) (I temp_7_1~587@))
                                    (=>
                                     (= temp_8_0~629@ (main!nl_basics.mul_.? (I (main!nl_basics.sub_.? (I a~2@) (I b~4@)))
                                       (I (main!nl_basics.mul_.? (I d~8@) (I b~4@)))
                                     ))
                                     (=>
                                      (= temp_8_1~659@ (main!nl_basics.sub_.? (I (main!nl_basics.mul_.? (I a~2@) (I (main!nl_basics.mul_.?
                                            (I d~8@) (I b~4@)
                                         )))
                                        ) (I (main!nl_basics.mul_.? (I b~4@) (I (main!nl_basics.mul_.? (I d~8@) (I b~4@)))))
                                      ))
                                      (and
                                       (=>
                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                        (=>
                                         %%location_label%%8
                                         (main!nl_basics.eq_.? (I temp_8_0~629@) (I temp_8_1~659@))
                                       ))
                                       (=>
                                        (main!nl_basics.eq_.? (I temp_8_0~629@) (I temp_8_1~659@))
                                        (=>
                                         (= temp_9_0~701@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I d~8@) (I b~4@)))
                                           (I (main!nl_basics.mul_.? (I c~6@) (I b~4@)))
                                         ))
                                         (=>
                                          (= temp_9_1~721@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I (main!nl_basics.mul_.?
                                                (I d~8@) (I b~4@)
                                               )
                                              ) (I c~6@)
                                             )
                                            ) (I b~4@)
                                          ))
                                          (and
                                           (=>
                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                            (=>
                                             %%location_label%%9
                                             (main!nl_basics.eq_.? (I temp_9_0~701@) (I temp_9_1~721@))
                                           ))
                                           (=>
                                            (main!nl_basics.eq_.? (I temp_9_0~701@) (I temp_9_1~721@))
                                            (=>
                                             (= temp_10_0~763@ (main!nl_basics.sub_.? (I (main!nl_basics.add_.? (I c~6@) (I b~4@)))
                                               (I (main!nl_basics.add_.? (I b~4@) (I d~8@)))
                                             ))
                                             (=>
                                              (= temp_10_1~783@ (main!nl_basics.sub_.? (I (main!nl_basics.add_.? (I c~6@) (I b~4@)))
                                                (I (main!nl_basics.add_.? (I d~8@) (I b~4@)))
                                              ))
                                              (and
                                               (=>
                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                (=>
                                                 %%location_label%%10
                                                 (main!nl_basics.eq_.? (I temp_10_0~763@) (I temp_10_1~783@))
                                               ))
                                               (=>
                                                (main!nl_basics.eq_.? (I temp_10_0~763@) (I temp_10_1~783@))
                                                (=>
                                                 (= temp_11_0~830@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I (main!nl_basics.mod_.?
                                                       (I c~6@) (I m~10@)
                                                      )
                                                     ) (I a~2@)
                                                    )
                                                   ) (I (main!nl_basics.mul_.? (I a~2@) (I a~2@)))
                                                 ))
                                                 (=>
                                                  (= temp_11_1~880@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I (main!nl_basics.mod_.?
                                                        (I (main!nl_basics.add_.? (I (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I (main!nl_basics.add_.?
                                                                (I c~6@) (I d~8@)
                                                               )
                                                              ) (I (main!nl_basics.mul_.? (I c~6@) (I c~6@)))
                                                             )
                                                            ) (I m~10@)
                                                           )
                                                          ) (I c~6@)
                                                         )
                                                        ) (I m~10@)
                                                       )
                                                      ) (I a~2@)
                                                     )
                                                    ) (I (main!nl_basics.mul_.? (I a~2@) (I a~2@)))
                                                  ))
                                                  (and
                                                   (=>
                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                    (=>
                                                     %%location_label%%11
                                                     (main!nl_basics.eq_.? (I temp_11_0~830@) (I temp_11_1~880@))
                                                   ))
                                                   (=>
                                                    (main!nl_basics.eq_.? (I temp_11_0~830@) (I temp_11_1~880@))
                                                    (=>
                                                     (= temp_12_0~927@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I d~8@) (I c~6@)))
                                                       (I (main!nl_basics.mod_.? (I (main!nl_basics.mul_.? (I b~4@) (I c~6@))) (I m~10@)))
                                                     ))
                                                     (=>
                                                      (= temp_12_1~952@ (main!nl_basics.mul_.? (I d~8@) (I (main!nl_basics.mul_.? (I c~6@)
                                                          (I (main!nl_basics.mod_.? (I (main!nl_basics.mul_.? (I b~4@) (I c~6@))) (I m~10@)))
                                                      ))))
                                                      (and
                                                       (=>
                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                        (=>
                                                         %%location_label%%12
                                                         (main!nl_basics.eq_.? (I temp_12_0~927@) (I temp_12_1~952@))
                                                       ))
                                                       (=>
                                                        (main!nl_basics.eq_.? (I temp_12_0~927@) (I temp_12_1~952@))
                                                        (=>
                                                         (= temp_13_0~994@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I d~8@) (I a~2@)))
                                                           (I (main!nl_basics.mul_.? (I d~8@) (I a~2@)))
                                                         ))
                                                         (=>
                                                          (= temp_13_1~1014@ (main!nl_basics.mul_.? (I d~8@) (I (main!nl_basics.mul_.? (I a~2@)
                                                              (I (main!nl_basics.mul_.? (I d~8@) (I a~2@)))
                                                          ))))
                                                          (and
                                                           (=>
                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                            (=>
                                                             %%location_label%%13
                                                             (main!nl_basics.eq_.? (I temp_13_0~994@) (I temp_13_1~1014@))
                                                           ))
                                                           (=>
                                                            (main!nl_basics.eq_.? (I temp_13_0~994@) (I temp_13_1~1014@))
                                                            (=>
                                                             (= temp_14_0~1061@ (main!nl_basics.add_.? (I (main!nl_basics.sub_.? (I d~8@) (I b~4@)))
                                                               (I (main!nl_basics.mod_.? (I (main!nl_basics.mul_.? (I c~6@) (I a~2@))) (I m~10@)))
                                                             ))
                                                             (=>
                                                              (= temp_14_1~1116@ (main!nl_basics.add_.? (I (main!nl_basics.sub_.? (I d~8@) (I b~4@)))
                                                                (I (main!nl_basics.mod_.? (I (main!nl_basics.sub_.? (I (main!nl_basics.mul_.? (I c~6@)
                                                                      (I a~2@)
                                                                     )
                                                                    ) (I (main!nl_basics.mul_.? (I (main!nl_basics.mod_.? (I (main!nl_basics.mul_.? (I (main!nl_basics.mul_.?
                                                                            (I a~2@) (I b~4@)
                                                                           )
                                                                          ) (I (main!nl_basics.mul_.? (I d~8@) (I b~4@)))
                                                                         )
                                                                        ) (I m~10@)
                                                                       )
                                                                      ) (I m~10@)
                                                                   )))
                                                                  ) (I m~10@)
                                                              ))))
                                                              (and
                                                               (=>
                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                (=>
                                                                 %%location_label%%14
                                                                 (main!nl_basics.eq_.? (I temp_14_0~1061@) (I temp_14_1~1116@))
                                                               ))
                                                               (=>
                                                                (main!nl_basics.eq_.? (I temp_14_0~1061@) (I temp_14_1~1116@))
                                                                (=>
                                                                 (= temp_15_0~1180@ (main!nl_basics.mul_.? (I (main!nl_basics.add_.? (I (main!nl_basics.mod_.?
                                                                       (I c~6@) (I m~10@)
                                                                      )
                                                                     ) (I (main!nl_basics.mod_.? (I 43) (I m~10@)))
                                                                    )
                                                                   ) (I (main!nl_basics.mul_.? (I a~2@) (I c~6@)))
                                                                 ))
                                                                 (=>
                                                                  (= temp_15_1~1269@ (main!nl_basics.mul_.? (I (main!nl_basics.add_.? (I (main!nl_basics.mod_.?
                                                                        (I c~6@) (I m~10@)
                                                                       )
                                                                      ) (I (main!nl_basics.mod_.? (I (main!nl_basics.add_.? (I 43) (I (main!nl_basics.mul_.?
                                                                            (I (main!nl_basics.mul_.? (I (main!nl_basics.mod_.? (I (main!nl_basics.mul_.? (I d~8@)
                                                                                  (I (main!nl_basics.mod_.? (I a~2@) (I m~10@)))
                                                                                 )
                                                                                ) (I m~10@)
                                                                               )
                                                                              ) (I (main!nl_basics.mul_.? (I b~4@) (I 22)))
                                                                             )
                                                                            ) (I m~10@)
                                                                         )))
                                                                        ) (I m~10@)
                                                                     )))
                                                                    ) (I (main!nl_basics.mul_.? (I a~2@) (I c~6@)))
                                                                  ))
                                                                  (and
                                                                   (=>
                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                    (=>
                                                                     %%location_label%%15
                                                                     (main!nl_basics.eq_.? (I temp_15_0~1180@) (I temp_15_1~1269@))
                                                                   ))
                                                                   (=>
                                                                    (main!nl_basics.eq_.? (I temp_15_0~1180@) (I temp_15_1~1269@))
                                                                    (=>
                                                                     (= temp_16_0~1323@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I b~4@) (I 75)))
                                                                       (I (main!nl_basics.mul_.? (I a~2@) (I d~8@)))
                                                                     ))
                                                                     (=>
                                                                      (= temp_16_1~1355@ (main!nl_basics.mul_.? (I b~4@) (I (main!nl_basics.mul_.? (I 75) (
                                                                           I (main!nl_basics.mul_.? (I a~2@) (I d~8@))
                                                                      )))))
                                                                      (and
                                                                       (=>
                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                        (=>
                                                                         %%location_label%%16
                                                                         (main!nl_basics.eq_.? (I temp_16_0~1323@) (I temp_16_1~1355@))
                                                                       ))
                                                                       (=>
                                                                        (main!nl_basics.eq_.? (I temp_16_0~1323@) (I temp_16_1~1355@))
                                                                        (=>
                                                                         (= temp_17_0~1402@ (main!nl_basics.mul_.? (I (main!nl_basics.sub_.? (I c~6@) (I b~4@)))
                                                                           (I (main!nl_basics.mod_.? (I (main!nl_basics.mul_.? (I c~6@) (I b~4@))) (I m~10@)))
                                                                         ))
                                                                         (=>
                                                                          (= temp_17_1~1427@ (main!nl_basics.mul_.? (I (main!nl_basics.sub_.? (I c~6@) (I b~4@)))
                                                                            (I (main!nl_basics.mod_.? (I (main!nl_basics.mul_.? (I b~4@) (I c~6@))) (I m~10@)))
                                                                          ))
                                                                          (and
                                                                           (=>
                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                            (=>
                                                                             %%location_label%%17
                                                                             (main!nl_basics.eq_.? (I temp_17_0~1402@) (I temp_17_1~1427@))
                                                                           ))
                                                                           (=>
                                                                            (main!nl_basics.eq_.? (I temp_17_0~1402@) (I temp_17_1~1427@))
                                                                            (=>
                                                                             (= temp_18_0~1469@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I d~8@) (I a~2@)))
                                                                               (I (main!nl_basics.mul_.? (I c~6@) (I b~4@)))
                                                                             ))
                                                                             (=>
                                                                              (= temp_18_1~1489@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I c~6@) (I b~4@)))
                                                                                (I (main!nl_basics.mul_.? (I d~8@) (I a~2@)))
                                                                              ))
                                                                              (and
                                                                               (=>
                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                (=>
                                                                                 %%location_label%%18
                                                                                 (main!nl_basics.eq_.? (I temp_18_0~1469@) (I temp_18_1~1489@))
                                                                               ))
                                                                               (=>
                                                                                (main!nl_basics.eq_.? (I temp_18_0~1469@) (I temp_18_1~1489@))
                                                                                (=>
                                                                                 (= temp_19_0~1536@ (main!nl_basics.mul_.? (I (main!nl_basics.mod_.? (I (main!nl_basics.mul_.?
                                                                                       (I c~6@) (I a~2@)
                                                                                      )
                                                                                     ) (I m~10@)
                                                                                    )
                                                                                   ) (I (main!nl_basics.mul_.? (I b~4@) (I c~6@)))
                                                                                 ))
                                                                                 (=>
                                                                                  (= temp_19_1~1561@ (main!nl_basics.mul_.? (I (main!nl_basics.mod_.? (I (main!nl_basics.mul_.?
                                                                                        (I a~2@) (I c~6@)
                                                                                       )
                                                                                      ) (I m~10@)
                                                                                     )
                                                                                    ) (I (main!nl_basics.mul_.? (I b~4@) (I c~6@)))
                                                                                  ))
                                                                                  (and
                                                                                   (=>
                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                    (=>
                                                                                     %%location_label%%19
                                                                                     (main!nl_basics.eq_.? (I temp_19_0~1536@) (I temp_19_1~1561@))
                                                                                   ))
                                                                                   (=>
                                                                                    (main!nl_basics.eq_.? (I temp_19_0~1536@) (I temp_19_1~1561@))
                                                                                    (=>
                                                                                     (= temp_20_0~1603@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I c~6@) (I b~4@)))
                                                                                       (I (main!nl_basics.add_.? (I a~2@) (I b~4@)))
                                                                                     ))
                                                                                     (=>
                                                                                      (= temp_20_1~1623@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I c~6@) (I b~4@)))
                                                                                        (I (main!nl_basics.add_.? (I b~4@) (I a~2@)))
                                                                                      ))
                                                                                      (and
                                                                                       (=>
                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                        (=>
                                                                                         %%location_label%%20
                                                                                         (main!nl_basics.eq_.? (I temp_20_0~1603@) (I temp_20_1~1623@))
                                                                                       ))
                                                                                       (=>
                                                                                        (main!nl_basics.eq_.? (I temp_20_0~1603@) (I temp_20_1~1623@))
                                                                                        (=>
                                                                                         (= temp_21_0~1670@ (main!nl_basics.mul_.? (I (main!nl_basics.mod_.? (I (main!nl_basics.mul_.?
                                                                                               (I d~8@) (I b~4@)
                                                                                              )
                                                                                             ) (I m~10@)
                                                                                            )
                                                                                           ) (I (main!nl_basics.add_.? (I b~4@) (I b~4@)))
                                                                                         ))
                                                                                         (=>
                                                                                          (= temp_21_1~1720@ (main!nl_basics.mul_.? (I (main!nl_basics.mod_.? (I (main!nl_basics.sub_.?
                                                                                                (I (main!nl_basics.mul_.? (I d~8@) (I b~4@))) (I (main!nl_basics.mul_.? (I (main!nl_basics.mul_.?
                                                                                                    (I (main!nl_basics.mul_.? (I d~8@) (I a~2@))) (I (main!nl_basics.sub_.? (I d~8@) (I
                                                                                                       b~4@
                                                                                                   ))))
                                                                                                  ) (I m~10@)
                                                                                               )))
                                                                                              ) (I m~10@)
                                                                                             )
                                                                                            ) (I (main!nl_basics.add_.? (I b~4@) (I b~4@)))
                                                                                          ))
                                                                                          (and
                                                                                           (=>
                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                            (=>
                                                                                             %%location_label%%21
                                                                                             (main!nl_basics.eq_.? (I temp_21_0~1670@) (I temp_21_1~1720@))
                                                                                           ))
                                                                                           (=>
                                                                                            (main!nl_basics.eq_.? (I temp_21_0~1670@) (I temp_21_1~1720@))
                                                                                            (=>
                                                                                             (= temp_22_0~1762@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I d~8@) (I d~8@)))
                                                                                               (I (main!nl_basics.mul_.? (I c~6@) (I d~8@)))
                                                                                             ))
                                                                                             (=>
                                                                                              (= temp_22_1~1782@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I (main!nl_basics.mul_.?
                                                                                                    (I d~8@) (I d~8@)
                                                                                                   )
                                                                                                  ) (I c~6@)
                                                                                                 )
                                                                                                ) (I d~8@)
                                                                                              ))
                                                                                              (and
                                                                                               (=>
                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                (=>
                                                                                                 %%location_label%%22
                                                                                                 (main!nl_basics.eq_.? (I temp_22_0~1762@) (I temp_22_1~1782@))
                                                                                               ))
                                                                                               (=>
                                                                                                (main!nl_basics.eq_.? (I temp_22_0~1762@) (I temp_22_1~1782@))
                                                                                                (=>
                                                                                                 (= temp_23_0~1841@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I b~4@) (I d~8@)))
                                                                                                   (I (main!nl_basics.mod_.? (I (main!nl_basics.mul_.? (I b~4@) (I 22))) (I m~10@)))
                                                                                                 ))
                                                                                                 (=>
                                                                                                  (= temp_23_1~1878@ (main!nl_basics.mul_.? (I b~4@) (I (main!nl_basics.mul_.? (I d~8@)
                                                                                                      (I (main!nl_basics.mod_.? (I (main!nl_basics.mul_.? (I b~4@) (I 22))) (I m~10@)))
                                                                                                  ))))
                                                                                                  (and
                                                                                                   (=>
                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                    (=>
                                                                                                     %%location_label%%23
                                                                                                     (main!nl_basics.eq_.? (I temp_23_0~1841@) (I temp_23_1~1878@))
                                                                                                   ))
                                                                                                   (=>
                                                                                                    (main!nl_basics.eq_.? (I temp_23_0~1841@) (I temp_23_1~1878@))
                                                                                                    (=>
                                                                                                     (= temp_24_0~1920@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I c~6@) (I c~6@)))
                                                                                                       (I (main!nl_basics.mul_.? (I a~2@) (I a~2@)))
                                                                                                     ))
                                                                                                     (=>
                                                                                                      (= temp_24_1~1940@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I (main!nl_basics.mul_.?
                                                                                                            (I c~6@) (I c~6@)
                                                                                                           )
                                                                                                          ) (I a~2@)
                                                                                                         )
                                                                                                        ) (I a~2@)
                                                                                                      ))
                                                                                                      (and
                                                                                                       (=>
                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                        (=>
                                                                                                         %%location_label%%24
                                                                                                         (main!nl_basics.eq_.? (I temp_24_0~1920@) (I temp_24_1~1940@))
                                                                                                       ))
                                                                                                       (=>
                                                                                                        (main!nl_basics.eq_.? (I temp_24_0~1920@) (I temp_24_1~1940@))
                                                                                                        (=>
                                                                                                         (= temp_25_0~1982@ (main!nl_basics.mul_.? (I (main!nl_basics.sub_.? (I d~8@) (I a~2@)))
                                                                                                           (I (main!nl_basics.mul_.? (I d~8@) (I c~6@)))
                                                                                                         ))
                                                                                                         (=>
                                                                                                          (= temp_25_1~2002@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I d~8@) (I c~6@)))
                                                                                                            (I (main!nl_basics.sub_.? (I d~8@) (I a~2@)))
                                                                                                          ))
                                                                                                          (and
                                                                                                           (=>
                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                            (=>
                                                                                                             %%location_label%%25
                                                                                                             (main!nl_basics.eq_.? (I temp_25_0~1982@) (I temp_25_1~2002@))
                                                                                                           ))
                                                                                                           (=>
                                                                                                            (main!nl_basics.eq_.? (I temp_25_0~1982@) (I temp_25_1~2002@))
                                                                                                            (=>
                                                                                                             (= temp_26_0~2051@ (main!nl_basics.sub_.? (I (main!nl_basics.add_.? (I 39) (I c~6@)))
                                                                                                               (I c~6@)
                                                                                                             ))
                                                                                                             (=>
                                                                                                              (= temp_26_1~2078@ (main!nl_basics.sub_.? (I (main!nl_basics.add_.? (I c~6@) (I 39)))
                                                                                                                (I c~6@)
                                                                                                              ))
                                                                                                              (and
                                                                                                               (=>
                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                (=>
                                                                                                                 %%location_label%%26
                                                                                                                 (main!nl_basics.eq_.? (I temp_26_0~2051@) (I temp_26_1~2078@))
                                                                                                               ))
                                                                                                               (=>
                                                                                                                (main!nl_basics.eq_.? (I temp_26_0~2051@) (I temp_26_1~2078@))
                                                                                                                (=>
                                                                                                                 (= temp_27_0~2130@ (main!nl_basics.add_.? (I (main!nl_basics.sub_.? (I (main!nl_basics.mod_.?
                                                                                                                       (I a~2@) (I m~10@)
                                                                                                                      )
                                                                                                                     ) (I (main!nl_basics.mod_.? (I a~2@) (I m~10@)))
                                                                                                                    )
                                                                                                                   ) (I (main!nl_basics.mod_.? (I c~6@) (I m~10@)))
                                                                                                                 ))
                                                                                                                 (=>
                                                                                                                  (= temp_27_1~2160@ (main!nl_basics.add_.? (I (main!nl_basics.mod_.? (I c~6@) (I m~10@)))
                                                                                                                    (I (main!nl_basics.sub_.? (I (main!nl_basics.mod_.? (I a~2@) (I m~10@))) (I (main!nl_basics.mod_.?
                                                                                                                        (I a~2@) (I m~10@)
                                                                                                                  ))))))
                                                                                                                  (and
                                                                                                                   (=>
                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                    (=>
                                                                                                                     %%location_label%%27
                                                                                                                     (main!nl_basics.eq_.? (I temp_27_0~2130@) (I temp_27_1~2160@))
                                                                                                                   ))
                                                                                                                   (=>
                                                                                                                    (main!nl_basics.eq_.? (I temp_27_0~2130@) (I temp_27_1~2160@))
                                                                                                                    (=>
                                                                                                                     (= temp_28_0~2212@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I (main!nl_basics.mod_.?
                                                                                                                           (I a~2@) (I m~10@)
                                                                                                                          )
                                                                                                                         ) (I (main!nl_basics.mod_.? (I c~6@) (I m~10@)))
                                                                                                                        )
                                                                                                                       ) (I (main!nl_basics.mul_.? (I d~8@) (I c~6@)))
                                                                                                                     ))
                                                                                                                     (=>
                                                                                                                      (= temp_28_1~2277@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I (main!nl_basics.mod_.?
                                                                                                                            (I a~2@) (I m~10@)
                                                                                                                           )
                                                                                                                          ) (I (main!nl_basics.mod_.? (I (main!nl_basics.add_.? (I (main!nl_basics.mul_.? (I (main!nl_basics.mul_.?
                                                                                                                                  (I (main!nl_basics.mul_.? (I (main!nl_basics.mod_.? (I a~2@) (I m~10@))) (I (main!nl_basics.mod_.?
                                                                                                                                      (I a~2@) (I m~10@)
                                                                                                                                   )))
                                                                                                                                  ) (I (main!nl_basics.mul_.? (I b~4@) (I c~6@)))
                                                                                                                                 )
                                                                                                                                ) (I m~10@)
                                                                                                                               )
                                                                                                                              ) (I c~6@)
                                                                                                                             )
                                                                                                                            ) (I m~10@)
                                                                                                                         )))
                                                                                                                        ) (I (main!nl_basics.mul_.? (I d~8@) (I c~6@)))
                                                                                                                      ))
                                                                                                                      (and
                                                                                                                       (=>
                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                        (=>
                                                                                                                         %%location_label%%28
                                                                                                                         (main!nl_basics.eq_.? (I temp_28_0~2212@) (I temp_28_1~2277@))
                                                                                                                       ))
                                                                                                                       (=>
                                                                                                                        (main!nl_basics.eq_.? (I temp_28_0~2212@) (I temp_28_1~2277@))
                                                                                                                        (=>
                                                                                                                         (= temp_29_0~2319@ (main!nl_basics.mul_.? (I (main!nl_basics.sub_.? (I d~8@) (I c~6@)))
                                                                                                                           (I (main!nl_basics.mul_.? (I d~8@) (I d~8@)))
                                                                                                                         ))
                                                                                                                         (=>
                                                                                                                          (= temp_29_1~2339@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I (main!nl_basics.sub_.?
                                                                                                                                (I d~8@) (I c~6@)
                                                                                                                               )
                                                                                                                              ) (I d~8@)
                                                                                                                             )
                                                                                                                            ) (I d~8@)
                                                                                                                          ))
                                                                                                                          (and
                                                                                                                           (=>
                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                            (=>
                                                                                                                             %%location_label%%29
                                                                                                                             (main!nl_basics.eq_.? (I temp_29_0~2319@) (I temp_29_1~2339@))
                                                                                                                           ))
                                                                                                                           (=>
                                                                                                                            (main!nl_basics.eq_.? (I temp_29_0~2319@) (I temp_29_1~2339@))
                                                                                                                            (=>
                                                                                                                             (= temp_30_0~2381@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I a~2@) (I b~4@)))
                                                                                                                               (I (main!nl_basics.mul_.? (I b~4@) (I d~8@)))
                                                                                                                             ))
                                                                                                                             (=>
                                                                                                                              (= temp_30_1~2401@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I b~4@) (I d~8@)))
                                                                                                                                (I (main!nl_basics.mul_.? (I a~2@) (I b~4@)))
                                                                                                                              ))
                                                                                                                              (and
                                                                                                                               (=>
                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                (=>
                                                                                                                                 %%location_label%%30
                                                                                                                                 (main!nl_basics.eq_.? (I temp_30_0~2381@) (I temp_30_1~2401@))
                                                                                                                               ))
                                                                                                                               (=>
                                                                                                                                (main!nl_basics.eq_.? (I temp_30_0~2381@) (I temp_30_1~2401@))
                                                                                                                                (=>
                                                                                                                                 (= temp_31_0~2448@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I (main!nl_basics.mod_.?
                                                                                                                                       (I a~2@) (I m~10@)
                                                                                                                                      )
                                                                                                                                     ) (I d~8@)
                                                                                                                                    )
                                                                                                                                   ) (I (main!nl_basics.mul_.? (I b~4@) (I c~6@)))
                                                                                                                                 ))
                                                                                                                                 (=>
                                                                                                                                  (= temp_31_1~2498@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I (main!nl_basics.mod_.?
                                                                                                                                        (I (main!nl_basics.sub_.? (I a~2@) (I (main!nl_basics.mul_.? (I (main!nl_basics.sub_.?
                                                                                                                                              (I (main!nl_basics.add_.? (I a~2@) (I a~2@))) (I (main!nl_basics.mul_.? (I d~8@) (I
                                                                                                                                                 b~4@
                                                                                                                                             ))))
                                                                                                                                            ) (I m~10@)
                                                                                                                                         )))
                                                                                                                                        ) (I m~10@)
                                                                                                                                       )
                                                                                                                                      ) (I d~8@)
                                                                                                                                     )
                                                                                                                                    ) (I (main!nl_basics.mul_.? (I b~4@) (I c~6@)))
                                                                                                                                  ))
                                                                                                                                  (and
                                                                                                                                   (=>
                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                    (=>
                                                                                                                                     %%location_label%%31
                                                                                                                                     (main!nl_basics.eq_.? (I temp_31_0~2448@) (I temp_31_1~2498@))
                                                                                                                                   ))
                                                                                                                                   (=>
                                                                                                                                    (main!nl_basics.eq_.? (I temp_31_0~2448@) (I temp_31_1~2498@))
                                                                                                                                    (=>
                                                                                                                                     (= temp_32_0~2540@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I b~4@) (I c~6@)))
                                                                                                                                       (I (main!nl_basics.mul_.? (I c~6@) (I d~8@)))
                                                                                                                                     ))
                                                                                                                                     (=>
                                                                                                                                      (= temp_32_1~2560@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I c~6@) (I d~8@)))
                                                                                                                                        (I (main!nl_basics.mul_.? (I b~4@) (I c~6@)))
                                                                                                                                      ))
                                                                                                                                      (and
                                                                                                                                       (=>
                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                        (=>
                                                                                                                                         %%location_label%%32
                                                                                                                                         (main!nl_basics.eq_.? (I temp_32_0~2540@) (I temp_32_1~2560@))
                                                                                                                                       ))
                                                                                                                                       (=>
                                                                                                                                        (main!nl_basics.eq_.? (I temp_32_0~2540@) (I temp_32_1~2560@))
                                                                                                                                        (=>
                                                                                                                                         (= temp_33_0~2607@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I c~6@) (I b~4@)))
                                                                                                                                           (I (main!nl_basics.mul_.? (I d~8@) (I (main!nl_basics.mod_.? (I b~4@) (I m~10@)))))
                                                                                                                                         ))
                                                                                                                                         (=>
                                                                                                                                          (= temp_33_1~2632@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I d~8@) (I (main!nl_basics.mod_.?
                                                                                                                                                (I b~4@) (I m~10@)
                                                                                                                                             )))
                                                                                                                                            ) (I (main!nl_basics.mul_.? (I c~6@) (I b~4@)))
                                                                                                                                          ))
                                                                                                                                          (and
                                                                                                                                           (=>
                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                            (=>
                                                                                                                                             %%location_label%%33
                                                                                                                                             (main!nl_basics.eq_.? (I temp_33_0~2607@) (I temp_33_1~2632@))
                                                                                                                                           ))
                                                                                                                                           (=>
                                                                                                                                            (main!nl_basics.eq_.? (I temp_33_0~2607@) (I temp_33_1~2632@))
                                                                                                                                            (=>
                                                                                                                                             (= temp_34_0~2674@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I b~4@) (I c~6@)))
                                                                                                                                               (I (main!nl_basics.add_.? (I a~2@) (I b~4@)))
                                                                                                                                             ))
                                                                                                                                             (=>
                                                                                                                                              (= temp_34_1~2694@ (main!nl_basics.mul_.? (I b~4@) (I (main!nl_basics.mul_.? (I c~6@)
                                                                                                                                                  (I (main!nl_basics.add_.? (I a~2@) (I b~4@)))
                                                                                                                                              ))))
                                                                                                                                              (and
                                                                                                                                               (=>
                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                (=>
                                                                                                                                                 %%location_label%%34
                                                                                                                                                 (main!nl_basics.eq_.? (I temp_34_0~2674@) (I temp_34_1~2694@))
                                                                                                                                               ))
                                                                                                                                               (=>
                                                                                                                                                (main!nl_basics.eq_.? (I temp_34_0~2674@) (I temp_34_1~2694@))
                                                                                                                                                (=>
                                                                                                                                                 (= temp_35_0~2753@ (main!nl_basics.add_.? (I (main!nl_basics.sub_.? (I (main!nl_basics.mod_.?
                                                                                                                                                       (I 36) (I m~10@)
                                                                                                                                                      )
                                                                                                                                                     ) (I d~8@)
                                                                                                                                                    )
                                                                                                                                                   ) (I (main!nl_basics.mul_.? (I b~4@) (I d~8@)))
                                                                                                                                                 ))
                                                                                                                                                 (=>
                                                                                                                                                  (= temp_35_1~2790@ (main!nl_basics.add_.? (I (main!nl_basics.sub_.? (I (main!nl_basics.mod_.?
                                                                                                                                                        (I 36) (I m~10@)
                                                                                                                                                       )
                                                                                                                                                      ) (I d~8@)
                                                                                                                                                     )
                                                                                                                                                    ) (I (main!nl_basics.mul_.? (I d~8@) (I b~4@)))
                                                                                                                                                  ))
                                                                                                                                                  (and
                                                                                                                                                   (=>
                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                    (=>
                                                                                                                                                     %%location_label%%35
                                                                                                                                                     (main!nl_basics.eq_.? (I temp_35_0~2753@) (I temp_35_1~2790@))
                                                                                                                                                   ))
                                                                                                                                                   (=>
                                                                                                                                                    (main!nl_basics.eq_.? (I temp_35_0~2753@) (I temp_35_1~2790@))
                                                                                                                                                    (=>
                                                                                                                                                     (= temp_36_0~2837@ (main!nl_basics.sub_.? (I (main!nl_basics.mod_.? (I (main!nl_basics.mul_.?
                                                                                                                                                           (I d~8@) (I a~2@)
                                                                                                                                                          )
                                                                                                                                                         ) (I m~10@)
                                                                                                                                                        )
                                                                                                                                                       ) (I (main!nl_basics.mul_.? (I b~4@) (I b~4@)))
                                                                                                                                                     ))
                                                                                                                                                     (=>
                                                                                                                                                      (= temp_36_1~2862@ (main!nl_basics.sub_.? (I (main!nl_basics.mod_.? (I (main!nl_basics.mul_.?
                                                                                                                                                            (I a~2@) (I d~8@)
                                                                                                                                                           )
                                                                                                                                                          ) (I m~10@)
                                                                                                                                                         )
                                                                                                                                                        ) (I (main!nl_basics.mul_.? (I b~4@) (I b~4@)))
                                                                                                                                                      ))
                                                                                                                                                      (and
                                                                                                                                                       (=>
                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                        (=>
                                                                                                                                                         %%location_label%%36
                                                                                                                                                         (main!nl_basics.eq_.? (I temp_36_0~2837@) (I temp_36_1~2862@))
                                                                                                                                                       ))
                                                                                                                                                       (=>
                                                                                                                                                        (main!nl_basics.eq_.? (I temp_36_0~2837@) (I temp_36_1~2862@))
                                                                                                                                                        (=>
                                                                                                                                                         (= temp_37_0~2909@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I d~8@) (I c~6@)))
                                                                                                                                                           (I (main!nl_basics.mul_.? (I b~4@) (I (main!nl_basics.mod_.? (I b~4@) (I m~10@)))))
                                                                                                                                                         ))
                                                                                                                                                         (=>
                                                                                                                                                          (= temp_37_1~2964@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I d~8@) (I c~6@)))
                                                                                                                                                            (I (main!nl_basics.mul_.? (I b~4@) (I (main!nl_basics.mod_.? (I (main!nl_basics.add_.?
                                                                                                                                                                  (I b~4@) (I (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I (main!nl_basics.sub_.?
                                                                                                                                                                        (I b~4@) (I c~6@)
                                                                                                                                                                       )
                                                                                                                                                                      ) (I (main!nl_basics.mod_.? (I (main!nl_basics.sub_.? (I c~6@) (I b~4@))) (I m~10@)))
                                                                                                                                                                     )
                                                                                                                                                                    ) (I m~10@)
                                                                                                                                                                 )))
                                                                                                                                                                ) (I m~10@)
                                                                                                                                                          ))))))
                                                                                                                                                          (and
                                                                                                                                                           (=>
                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                            (=>
                                                                                                                                                             %%location_label%%37
                                                                                                                                                             (main!nl_basics.eq_.? (I temp_37_0~2909@) (I temp_37_1~2964@))
                                                                                                                                                           ))
                                                                                                                                                           (=>
                                                                                                                                                            (main!nl_basics.eq_.? (I temp_37_0~2909@) (I temp_37_1~2964@))
                                                                                                                                                            (=>
                                                                                                                                                             (= temp_38_0~3006@ (main!nl_basics.sub_.? (I (main!nl_basics.add_.? (I d~8@) (I d~8@)))
                                                                                                                                                               (I (main!nl_basics.mul_.? (I c~6@) (I a~2@)))
                                                                                                                                                             ))
                                                                                                                                                             (=>
                                                                                                                                                              (= temp_38_1~3026@ (main!nl_basics.sub_.? (I (main!nl_basics.add_.? (I d~8@) (I d~8@)))
                                                                                                                                                                (I (main!nl_basics.mul_.? (I a~2@) (I c~6@)))
                                                                                                                                                              ))
                                                                                                                                                              (and
                                                                                                                                                               (=>
                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                (=>
                                                                                                                                                                 %%location_label%%38
                                                                                                                                                                 (main!nl_basics.eq_.? (I temp_38_0~3006@) (I temp_38_1~3026@))
                                                                                                                                                               ))
                                                                                                                                                               (=>
                                                                                                                                                                (main!nl_basics.eq_.? (I temp_38_0~3006@) (I temp_38_1~3026@))
                                                                                                                                                                (=>
                                                                                                                                                                 (= temp_39_0~3068@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I d~8@) (I a~2@)))
                                                                                                                                                                   (I (main!nl_basics.mul_.? (I b~4@) (I d~8@)))
                                                                                                                                                                 ))
                                                                                                                                                                 (=>
                                                                                                                                                                  (= temp_39_1~3088@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I (main!nl_basics.mul_.?
                                                                                                                                                                        (I d~8@) (I a~2@)
                                                                                                                                                                       )
                                                                                                                                                                      ) (I b~4@)
                                                                                                                                                                     )
                                                                                                                                                                    ) (I d~8@)
                                                                                                                                                                  ))
                                                                                                                                                                  (and
                                                                                                                                                                   (=>
                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                    (=>
                                                                                                                                                                     %%location_label%%39
                                                                                                                                                                     (main!nl_basics.eq_.? (I temp_39_0~3068@) (I temp_39_1~3088@))
                                                                                                                                                                   ))
                                                                                                                                                                   (=>
                                                                                                                                                                    (main!nl_basics.eq_.? (I temp_39_0~3068@) (I temp_39_1~3088@))
                                                                                                                                                                    (=>
                                                                                                                                                                     (= temp_40_0~3130@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I a~2@) (I c~6@)))
                                                                                                                                                                       (I (main!nl_basics.mul_.? (I d~8@) (I b~4@)))
                                                                                                                                                                     ))
                                                                                                                                                                     (=>
                                                                                                                                                                      (= temp_40_1~3150@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I (main!nl_basics.mul_.?
                                                                                                                                                                            (I a~2@) (I c~6@)
                                                                                                                                                                           )
                                                                                                                                                                          ) (I d~8@)
                                                                                                                                                                         )
                                                                                                                                                                        ) (I b~4@)
                                                                                                                                                                      ))
                                                                                                                                                                      (and
                                                                                                                                                                       (=>
                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                        (=>
                                                                                                                                                                         %%location_label%%40
                                                                                                                                                                         (main!nl_basics.eq_.? (I temp_40_0~3130@) (I temp_40_1~3150@))
                                                                                                                                                                       ))
                                                                                                                                                                       (=>
                                                                                                                                                                        (main!nl_basics.eq_.? (I temp_40_0~3130@) (I temp_40_1~3150@))
                                                                                                                                                                        (=>
                                                                                                                                                                         (= temp_41_0~3192@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I d~8@) (I a~2@)))
                                                                                                                                                                           (I (main!nl_basics.mul_.? (I b~4@) (I b~4@)))
                                                                                                                                                                         ))
                                                                                                                                                                         (=>
                                                                                                                                                                          (= temp_41_1~3212@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I d~8@) (I a~2@)))
                                                                                                                                                                            (I (main!nl_basics.mul_.? (I b~4@) (I b~4@)))
                                                                                                                                                                          ))
                                                                                                                                                                          (and
                                                                                                                                                                           (=>
                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                            (=>
                                                                                                                                                                             %%location_label%%41
                                                                                                                                                                             (main!nl_basics.eq_.? (I temp_41_0~3192@) (I temp_41_1~3212@))
                                                                                                                                                                           ))
                                                                                                                                                                           (=>
                                                                                                                                                                            (main!nl_basics.eq_.? (I temp_41_0~3192@) (I temp_41_1~3212@))
                                                                                                                                                                            (=>
                                                                                                                                                                             (= temp_42_0~3254@ (main!nl_basics.mul_.? (I (main!nl_basics.sub_.? (I d~8@) (I a~2@)))
                                                                                                                                                                               (I (main!nl_basics.sub_.? (I a~2@) (I a~2@)))
                                                                                                                                                                             ))
                                                                                                                                                                             (=>
                                                                                                                                                                              (= temp_42_1~3284@ (main!nl_basics.sub_.? (I (main!nl_basics.mul_.? (I d~8@) (I (main!nl_basics.sub_.?
                                                                                                                                                                                    (I a~2@) (I a~2@)
                                                                                                                                                                                 )))
                                                                                                                                                                                ) (I (main!nl_basics.mul_.? (I a~2@) (I (main!nl_basics.sub_.? (I a~2@) (I a~2@)))))
                                                                                                                                                                              ))
                                                                                                                                                                              (and
                                                                                                                                                                               (=>
                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                (=>
                                                                                                                                                                                 %%location_label%%42
                                                                                                                                                                                 (main!nl_basics.eq_.? (I temp_42_0~3254@) (I temp_42_1~3284@))
                                                                                                                                                                               ))
                                                                                                                                                                               (=>
                                                                                                                                                                                (main!nl_basics.eq_.? (I temp_42_0~3254@) (I temp_42_1~3284@))
                                                                                                                                                                                (=>
                                                                                                                                                                                 (= temp_43_0~3326@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I d~8@) (I a~2@)))
                                                                                                                                                                                   (I (main!nl_basics.mul_.? (I d~8@) (I b~4@)))
                                                                                                                                                                                 ))
                                                                                                                                                                                 (=>
                                                                                                                                                                                  (= temp_43_1~3346@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I d~8@) (I a~2@)))
                                                                                                                                                                                    (I (main!nl_basics.mul_.? (I b~4@) (I d~8@)))
                                                                                                                                                                                  ))
                                                                                                                                                                                  (and
                                                                                                                                                                                   (=>
                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                    (=>
                                                                                                                                                                                     %%location_label%%43
                                                                                                                                                                                     (main!nl_basics.eq_.? (I temp_43_0~3326@) (I temp_43_1~3346@))
                                                                                                                                                                                   ))
                                                                                                                                                                                   (=>
                                                                                                                                                                                    (main!nl_basics.eq_.? (I temp_43_0~3326@) (I temp_43_1~3346@))
                                                                                                                                                                                    (=>
                                                                                                                                                                                     (= temp_44_0~3393@ (main!nl_basics.mul_.? (I (main!nl_basics.add_.? (I a~2@) (I (main!nl_basics.mod_.?
                                                                                                                                                                                           (I a~2@) (I m~10@)
                                                                                                                                                                                        )))
                                                                                                                                                                                       ) (I (main!nl_basics.add_.? (I b~4@) (I a~2@)))
                                                                                                                                                                                     ))
                                                                                                                                                                                     (=>
                                                                                                                                                                                      (= temp_44_1~3433@ (main!nl_basics.add_.? (I (main!nl_basics.mul_.? (I (main!nl_basics.add_.?
                                                                                                                                                                                            (I a~2@) (I (main!nl_basics.mod_.? (I a~2@) (I m~10@)))
                                                                                                                                                                                           )
                                                                                                                                                                                          ) (I b~4@)
                                                                                                                                                                                         )
                                                                                                                                                                                        ) (I (main!nl_basics.mul_.? (I (main!nl_basics.add_.? (I a~2@) (I (main!nl_basics.mod_.?
                                                                                                                                                                                              (I a~2@) (I m~10@)
                                                                                                                                                                                           )))
                                                                                                                                                                                          ) (I a~2@)
                                                                                                                                                                                      ))))
                                                                                                                                                                                      (and
                                                                                                                                                                                       (=>
                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                        (=>
                                                                                                                                                                                         %%location_label%%44
                                                                                                                                                                                         (main!nl_basics.eq_.? (I temp_44_0~3393@) (I temp_44_1~3433@))
                                                                                                                                                                                       ))
                                                                                                                                                                                       (=>
                                                                                                                                                                                        (main!nl_basics.eq_.? (I temp_44_0~3393@) (I temp_44_1~3433@))
                                                                                                                                                                                        (=>
                                                                                                                                                                                         (= temp_45_0~3475@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I c~6@) (I b~4@)))
                                                                                                                                                                                           (I (main!nl_basics.mul_.? (I c~6@) (I d~8@)))
                                                                                                                                                                                         ))
                                                                                                                                                                                         (=>
                                                                                                                                                                                          (= temp_45_1~3495@ (main!nl_basics.mul_.? (I c~6@) (I (main!nl_basics.mul_.? (I b~4@)
                                                                                                                                                                                              (I (main!nl_basics.mul_.? (I c~6@) (I d~8@)))
                                                                                                                                                                                          ))))
                                                                                                                                                                                          (and
                                                                                                                                                                                           (=>
                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                            (=>
                                                                                                                                                                                             %%location_label%%45
                                                                                                                                                                                             (main!nl_basics.eq_.? (I temp_45_0~3475@) (I temp_45_1~3495@))
                                                                                                                                                                                           ))
                                                                                                                                                                                           (=>
                                                                                                                                                                                            (main!nl_basics.eq_.? (I temp_45_0~3475@) (I temp_45_1~3495@))
                                                                                                                                                                                            (=>
                                                                                                                                                                                             (= temp_46_0~3552@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I (main!nl_basics.mod_.?
                                                                                                                                                                                                   (I a~2@) (I m~10@)
                                                                                                                                                                                                  )
                                                                                                                                                                                                 ) (I d~8@)
                                                                                                                                                                                                )
                                                                                                                                                                                               ) (I (main!nl_basics.mul_.? (I (main!nl_basics.mod_.? (I a~2@) (I m~10@))) (I (main!nl_basics.mod_.?
                                                                                                                                                                                                   (I b~4@) (I m~10@)
                                                                                                                                                                                             ))))))
                                                                                                                                                                                             (=>
                                                                                                                                                                                              (= temp_46_1~3587@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I (main!nl_basics.mul_.?
                                                                                                                                                                                                    (I (main!nl_basics.mod_.? (I a~2@) (I m~10@))) (I d~8@)
                                                                                                                                                                                                   )
                                                                                                                                                                                                  ) (I (main!nl_basics.mod_.? (I a~2@) (I m~10@)))
                                                                                                                                                                                                 )
                                                                                                                                                                                                ) (I (main!nl_basics.mod_.? (I b~4@) (I m~10@)))
                                                                                                                                                                                              ))
                                                                                                                                                                                              (and
                                                                                                                                                                                               (=>
                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                (=>
                                                                                                                                                                                                 %%location_label%%46
                                                                                                                                                                                                 (main!nl_basics.eq_.? (I temp_46_0~3552@) (I temp_46_1~3587@))
                                                                                                                                                                                               ))
                                                                                                                                                                                               (=>
                                                                                                                                                                                                (main!nl_basics.eq_.? (I temp_46_0~3552@) (I temp_46_1~3587@))
                                                                                                                                                                                                (=>
                                                                                                                                                                                                 (= temp_47_0~3629@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I b~4@) (I b~4@)))
                                                                                                                                                                                                   (I (main!nl_basics.add_.? (I d~8@) (I d~8@)))
                                                                                                                                                                                                 ))
                                                                                                                                                                                                 (=>
                                                                                                                                                                                                  (= temp_47_1~3649@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I b~4@) (I b~4@)))
                                                                                                                                                                                                    (I (main!nl_basics.add_.? (I d~8@) (I d~8@)))
                                                                                                                                                                                                  ))
                                                                                                                                                                                                  (and
                                                                                                                                                                                                   (=>
                                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                    (=>
                                                                                                                                                                                                     %%location_label%%47
                                                                                                                                                                                                     (main!nl_basics.eq_.? (I temp_47_0~3629@) (I temp_47_1~3649@))
                                                                                                                                                                                                   ))
                                                                                                                                                                                                   (=>
                                                                                                                                                                                                    (main!nl_basics.eq_.? (I temp_47_0~3629@) (I temp_47_1~3649@))
                                                                                                                                                                                                    (=>
                                                                                                                                                                                                     (= temp_48_0~3701@ (main!nl_basics.mul_.? (I (main!nl_basics.add_.? (I d~8@) (I (main!nl_basics.mod_.?
                                                                                                                                                                                                           (I b~4@) (I m~10@)
                                                                                                                                                                                                        )))
                                                                                                                                                                                                       ) (I (main!nl_basics.mod_.? (I (main!nl_basics.mul_.? (I b~4@) (I d~8@))) (I m~10@)))
                                                                                                                                                                                                     ))
                                                                                                                                                                                                     (=>
                                                                                                                                                                                                      (= temp_48_1~3731@ (main!nl_basics.mul_.? (I (main!nl_basics.add_.? (I d~8@) (I (main!nl_basics.mod_.?
                                                                                                                                                                                                            (I b~4@) (I m~10@)
                                                                                                                                                                                                         )))
                                                                                                                                                                                                        ) (I (main!nl_basics.mod_.? (I (main!nl_basics.mul_.? (I d~8@) (I b~4@))) (I m~10@)))
                                                                                                                                                                                                      ))
                                                                                                                                                                                                      (and
                                                                                                                                                                                                       (=>
                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                        (=>
                                                                                                                                                                                                         %%location_label%%48
                                                                                                                                                                                                         (main!nl_basics.eq_.? (I temp_48_0~3701@) (I temp_48_1~3731@))
                                                                                                                                                                                                       ))
                                                                                                                                                                                                       (=>
                                                                                                                                                                                                        (main!nl_basics.eq_.? (I temp_48_0~3701@) (I temp_48_1~3731@))
                                                                                                                                                                                                        (=>
                                                                                                                                                                                                         (= temp_49_0~3783@ (main!nl_basics.mul_.? (I (main!nl_basics.mod_.? (I (main!nl_basics.sub_.?
                                                                                                                                                                                                               (I a~2@) (I b~4@)
                                                                                                                                                                                                              )
                                                                                                                                                                                                             ) (I m~10@)
                                                                                                                                                                                                            )
                                                                                                                                                                                                           ) (I (main!nl_basics.add_.? (I (main!nl_basics.mod_.? (I c~6@) (I m~10@))) (I d~8@)))
                                                                                                                                                                                                         ))
                                                                                                                                                                                                         (=>
                                                                                                                                                                                                          (= temp_49_1~3813@ (main!nl_basics.mul_.? (I (main!nl_basics.mod_.? (I (main!nl_basics.sub_.?
                                                                                                                                                                                                                (I a~2@) (I b~4@)
                                                                                                                                                                                                               )
                                                                                                                                                                                                              ) (I m~10@)
                                                                                                                                                                                                             )
                                                                                                                                                                                                            ) (I (main!nl_basics.add_.? (I d~8@) (I (main!nl_basics.mod_.? (I c~6@) (I m~10@)))))
                                                                                                                                                                                                          ))
                                                                                                                                                                                                          (and
                                                                                                                                                                                                           (=>
                                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                            (=>
                                                                                                                                                                                                             %%location_label%%49
                                                                                                                                                                                                             (main!nl_basics.eq_.? (I temp_49_0~3783@) (I temp_49_1~3813@))
                                                                                                                                                                                                           ))
                                                                                                                                                                                                           (=>
                                                                                                                                                                                                            (main!nl_basics.eq_.? (I temp_49_0~3783@) (I temp_49_1~3813@))
                                                                                                                                                                                                            (=>
                                                                                                                                                                                                             (= temp_50_0~3860@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I c~6@) (I c~6@)))
                                                                                                                                                                                                               (I (main!nl_basics.add_.? (I b~4@) (I (main!nl_basics.mod_.? (I b~4@) (I m~10@)))))
                                                                                                                                                                                                             ))
                                                                                                                                                                                                             (=>
                                                                                                                                                                                                              (= temp_50_1~3895@ (main!nl_basics.add_.? (I (main!nl_basics.mul_.? (I (main!nl_basics.mul_.?
                                                                                                                                                                                                                    (I c~6@) (I c~6@)
                                                                                                                                                                                                                   )
                                                                                                                                                                                                                  ) (I b~4@)
                                                                                                                                                                                                                 )
                                                                                                                                                                                                                ) (I (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I c~6@) (I c~6@))) (I (main!nl_basics.mod_.?
                                                                                                                                                                                                                    (I b~4@) (I m~10@)
                                                                                                                                                                                                              ))))))
                                                                                                                                                                                                              (and
                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                 %%location_label%%50
                                                                                                                                                                                                                 (main!nl_basics.eq_.? (I temp_50_0~3860@) (I temp_50_1~3895@))
                                                                                                                                                                                                               ))
                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                (main!nl_basics.eq_.? (I temp_50_0~3860@) (I temp_50_1~3895@))
                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                 (= temp_51_0~3947@ (main!nl_basics.mul_.? (I (main!nl_basics.sub_.? (I (main!nl_basics.mod_.?
                                                                                                                                                                                                                       (I d~8@) (I m~10@)
                                                                                                                                                                                                                      )
                                                                                                                                                                                                                     ) (I (main!nl_basics.mod_.? (I b~4@) (I m~10@)))
                                                                                                                                                                                                                    )
                                                                                                                                                                                                                   ) (I (main!nl_basics.mul_.? (I d~8@) (I d~8@)))
                                                                                                                                                                                                                 ))
                                                                                                                                                                                                                 (=>
                                                                                                                                                                                                                  (= temp_51_1~3977@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I (main!nl_basics.sub_.?
                                                                                                                                                                                                                        (I (main!nl_basics.mod_.? (I d~8@) (I m~10@))) (I (main!nl_basics.mod_.? (I b~4@) (
                                                                                                                                                                                                                           I m~10@
                                                                                                                                                                                                                       ))))
                                                                                                                                                                                                                      ) (I d~8@)
                                                                                                                                                                                                                     )
                                                                                                                                                                                                                    ) (I d~8@)
                                                                                                                                                                                                                  ))
                                                                                                                                                                                                                  (and
                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                     %%location_label%%51
                                                                                                                                                                                                                     (main!nl_basics.eq_.? (I temp_51_0~3947@) (I temp_51_1~3977@))
                                                                                                                                                                                                                   ))
                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                    (main!nl_basics.eq_.? (I temp_51_0~3947@) (I temp_51_1~3977@))
                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                     (= temp_52_0~4031@ (main!nl_basics.add_.? (I (main!nl_basics.mul_.? (I b~4@) (I 53)))
                                                                                                                                                                                                                       (I (main!nl_basics.mul_.? (I a~2@) (I a~2@)))
                                                                                                                                                                                                                     ))
                                                                                                                                                                                                                     (=>
                                                                                                                                                                                                                      (= temp_52_1~4063@ (main!nl_basics.add_.? (I (main!nl_basics.mul_.? (I a~2@) (I a~2@)))
                                                                                                                                                                                                                        (I (main!nl_basics.mul_.? (I b~4@) (I 53)))
                                                                                                                                                                                                                      ))
                                                                                                                                                                                                                      (and
                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                         %%location_label%%52
                                                                                                                                                                                                                         (main!nl_basics.eq_.? (I temp_52_0~4031@) (I temp_52_1~4063@))
                                                                                                                                                                                                                       ))
                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                        (main!nl_basics.eq_.? (I temp_52_0~4031@) (I temp_52_1~4063@))
                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                         (= temp_53_0~4117@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I b~4@) (I c~6@)))
                                                                                                                                                                                                                           (I (main!nl_basics.mul_.? (I c~6@) (I 78)))
                                                                                                                                                                                                                         ))
                                                                                                                                                                                                                         (=>
                                                                                                                                                                                                                          (= temp_53_1~4149@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I (main!nl_basics.mul_.?
                                                                                                                                                                                                                                (I b~4@) (I c~6@)
                                                                                                                                                                                                                               )
                                                                                                                                                                                                                              ) (I c~6@)
                                                                                                                                                                                                                             )
                                                                                                                                                                                                                            ) (I 78)
                                                                                                                                                                                                                          ))
                                                                                                                                                                                                                          (and
                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                             %%location_label%%53
                                                                                                                                                                                                                             (main!nl_basics.eq_.? (I temp_53_0~4117@) (I temp_53_1~4149@))
                                                                                                                                                                                                                           ))
                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                            (main!nl_basics.eq_.? (I temp_53_0~4117@) (I temp_53_1~4149@))
                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                             (= temp_54_0~4191@ (main!nl_basics.mul_.? (I (main!nl_basics.sub_.? (I c~6@) (I c~6@)))
                                                                                                                                                                                                                               (I (main!nl_basics.mul_.? (I b~4@) (I a~2@)))
                                                                                                                                                                                                                             ))
                                                                                                                                                                                                                             (=>
                                                                                                                                                                                                                              (= temp_54_1~4221@ (main!nl_basics.sub_.? (I (main!nl_basics.mul_.? (I c~6@) (I (main!nl_basics.mul_.?
                                                                                                                                                                                                                                    (I b~4@) (I a~2@)
                                                                                                                                                                                                                                 )))
                                                                                                                                                                                                                                ) (I (main!nl_basics.mul_.? (I c~6@) (I (main!nl_basics.mul_.? (I b~4@) (I a~2@)))))
                                                                                                                                                                                                                              ))
                                                                                                                                                                                                                              (and
                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                 %%location_label%%54
                                                                                                                                                                                                                                 (main!nl_basics.eq_.? (I temp_54_0~4191@) (I temp_54_1~4221@))
                                                                                                                                                                                                                               ))
                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                (main!nl_basics.eq_.? (I temp_54_0~4191@) (I temp_54_1~4221@))
                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                 (= temp_55_0~4263@ (main!nl_basics.mul_.? (I (main!nl_basics.add_.? (I a~2@) (I b~4@)))
                                                                                                                                                                                                                                   (I (main!nl_basics.mul_.? (I c~6@) (I a~2@)))
                                                                                                                                                                                                                                 ))
                                                                                                                                                                                                                                 (=>
                                                                                                                                                                                                                                  (= temp_55_1~4283@ (main!nl_basics.mul_.? (I (main!nl_basics.add_.? (I b~4@) (I a~2@)))
                                                                                                                                                                                                                                    (I (main!nl_basics.mul_.? (I c~6@) (I a~2@)))
                                                                                                                                                                                                                                  ))
                                                                                                                                                                                                                                  (and
                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                     %%location_label%%55
                                                                                                                                                                                                                                     (main!nl_basics.eq_.? (I temp_55_0~4263@) (I temp_55_1~4283@))
                                                                                                                                                                                                                                   ))
                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                    (main!nl_basics.eq_.? (I temp_55_0~4263@) (I temp_55_1~4283@))
                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                     (= temp_56_0~4337@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I a~2@) (I c~6@)))
                                                                                                                                                                                                                                       (I (main!nl_basics.mul_.? (I 41) (I d~8@)))
                                                                                                                                                                                                                                     ))
                                                                                                                                                                                                                                     (=>
                                                                                                                                                                                                                                      (= temp_56_1~4369@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I a~2@) (I c~6@)))
                                                                                                                                                                                                                                        (I (main!nl_basics.mul_.? (I d~8@) (I 41)))
                                                                                                                                                                                                                                      ))
                                                                                                                                                                                                                                      (and
                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                         %%location_label%%56
                                                                                                                                                                                                                                         (main!nl_basics.eq_.? (I temp_56_0~4337@) (I temp_56_1~4369@))
                                                                                                                                                                                                                                       ))
                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                        (main!nl_basics.eq_.? (I temp_56_0~4337@) (I temp_56_1~4369@))
                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                         (= temp_57_0~4411@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I d~8@) (I c~6@)))
                                                                                                                                                                                                                                           (I (main!nl_basics.mul_.? (I a~2@) (I b~4@)))
                                                                                                                                                                                                                                         ))
                                                                                                                                                                                                                                         (=>
                                                                                                                                                                                                                                          (= temp_57_1~4431@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I c~6@) (I d~8@)))
                                                                                                                                                                                                                                            (I (main!nl_basics.mul_.? (I a~2@) (I b~4@)))
                                                                                                                                                                                                                                          ))
                                                                                                                                                                                                                                          (and
                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                             %%location_label%%57
                                                                                                                                                                                                                                             (main!nl_basics.eq_.? (I temp_57_0~4411@) (I temp_57_1~4431@))
                                                                                                                                                                                                                                           ))
                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                            (main!nl_basics.eq_.? (I temp_57_0~4411@) (I temp_57_1~4431@))
                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                             (= temp_58_0~4478@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I b~4@) (I (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                   (I a~2@) (I m~10@)
                                                                                                                                                                                                                                                )))
                                                                                                                                                                                                                                               ) (I (main!nl_basics.mul_.? (I b~4@) (I d~8@)))
                                                                                                                                                                                                                                             ))
                                                                                                                                                                                                                                             (=>
                                                                                                                                                                                                                                              (= temp_58_1~4528@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I b~4@) (I (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                    (I (main!nl_basics.add_.? (I a~2@) (I (main!nl_basics.mul_.? (I (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                          (I (main!nl_basics.mul_.? (I d~8@) (I a~2@))) (I (main!nl_basics.mul_.? (I d~8@) (I
                                                                                                                                                                                                                                                             d~8@
                                                                                                                                                                                                                                                         ))))
                                                                                                                                                                                                                                                        ) (I m~10@)
                                                                                                                                                                                                                                                     )))
                                                                                                                                                                                                                                                    ) (I m~10@)
                                                                                                                                                                                                                                                 )))
                                                                                                                                                                                                                                                ) (I (main!nl_basics.mul_.? (I b~4@) (I d~8@)))
                                                                                                                                                                                                                                              ))
                                                                                                                                                                                                                                              (and
                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                 %%location_label%%58
                                                                                                                                                                                                                                                 (main!nl_basics.eq_.? (I temp_58_0~4478@) (I temp_58_1~4528@))
                                                                                                                                                                                                                                               ))
                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                (main!nl_basics.eq_.? (I temp_58_0~4478@) (I temp_58_1~4528@))
                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                 (= temp_59_0~4575@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I c~6@) (I (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                       (I d~8@) (I m~10@)
                                                                                                                                                                                                                                                    )))
                                                                                                                                                                                                                                                   ) (I (main!nl_basics.mul_.? (I c~6@) (I b~4@)))
                                                                                                                                                                                                                                                 ))
                                                                                                                                                                                                                                                 (=>
                                                                                                                                                                                                                                                  (= temp_59_1~4600@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I c~6@) (I b~4@)))
                                                                                                                                                                                                                                                    (I (main!nl_basics.mul_.? (I c~6@) (I (main!nl_basics.mod_.? (I d~8@) (I m~10@)))))
                                                                                                                                                                                                                                                  ))
                                                                                                                                                                                                                                                  (and
                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                     %%location_label%%59
                                                                                                                                                                                                                                                     (main!nl_basics.eq_.? (I temp_59_0~4575@) (I temp_59_1~4600@))
                                                                                                                                                                                                                                                   ))
                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                    (main!nl_basics.eq_.? (I temp_59_0~4575@) (I temp_59_1~4600@))
                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                     (= temp_60_0~4652@ (main!nl_basics.mul_.? (I (main!nl_basics.mod_.? (I (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                           (I a~2@) (I (main!nl_basics.mod_.? (I a~2@) (I m~10@)))
                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                         ) (I m~10@)
                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                       ) (I (main!nl_basics.mul_.? (I c~6@) (I a~2@)))
                                                                                                                                                                                                                                                     ))
                                                                                                                                                                                                                                                     (=>
                                                                                                                                                                                                                                                      (= temp_60_1~4707@ (main!nl_basics.mul_.? (I (main!nl_basics.mod_.? (I (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                            (I a~2@) (I (main!nl_basics.mod_.? (I (main!nl_basics.add_.? (I (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                  (I (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I b~4@) (I c~6@))) (I (main!nl_basics.sub_.?
                                                                                                                                                                                                                                                                      (I d~8@) (I a~2@)
                                                                                                                                                                                                                                                                   )))
                                                                                                                                                                                                                                                                  ) (I m~10@)
                                                                                                                                                                                                                                                                 )
                                                                                                                                                                                                                                                                ) (I a~2@)
                                                                                                                                                                                                                                                               )
                                                                                                                                                                                                                                                              ) (I m~10@)
                                                                                                                                                                                                                                                           )))
                                                                                                                                                                                                                                                          ) (I m~10@)
                                                                                                                                                                                                                                                         )
                                                                                                                                                                                                                                                        ) (I (main!nl_basics.mul_.? (I c~6@) (I a~2@)))
                                                                                                                                                                                                                                                      ))
                                                                                                                                                                                                                                                      (and
                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                         %%location_label%%60
                                                                                                                                                                                                                                                         (main!nl_basics.eq_.? (I temp_60_0~4652@) (I temp_60_1~4707@))
                                                                                                                                                                                                                                                       ))
                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                        (main!nl_basics.eq_.? (I temp_60_0~4652@) (I temp_60_1~4707@))
                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                         (= temp_61_0~4761@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I 66) (I c~6@)))
                                                                                                                                                                                                                                                           (I (main!nl_basics.add_.? (I a~2@) (I d~8@)))
                                                                                                                                                                                                                                                         ))
                                                                                                                                                                                                                                                         (=>
                                                                                                                                                                                                                                                          (= temp_61_1~4793@ (main!nl_basics.mul_.? (I 66) (I (main!nl_basics.mul_.? (I c~6@) (
                                                                                                                                                                                                                                                               I (main!nl_basics.add_.? (I a~2@) (I d~8@))
                                                                                                                                                                                                                                                          )))))
                                                                                                                                                                                                                                                          (and
                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                             %%location_label%%61
                                                                                                                                                                                                                                                             (main!nl_basics.eq_.? (I temp_61_0~4761@) (I temp_61_1~4793@))
                                                                                                                                                                                                                                                           ))
                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                            (main!nl_basics.eq_.? (I temp_61_0~4761@) (I temp_61_1~4793@))
                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                             (= temp_62_0~4830@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I c~6@) (I b~4@)))
                                                                                                                                                                                                                                                               (I d~8@)
                                                                                                                                                                                                                                                             ))
                                                                                                                                                                                                                                                             (=>
                                                                                                                                                                                                                                                              (= temp_62_1~4845@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I b~4@) (I c~6@)))
                                                                                                                                                                                                                                                                (I d~8@)
                                                                                                                                                                                                                                                              ))
                                                                                                                                                                                                                                                              (and
                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                 %%location_label%%62
                                                                                                                                                                                                                                                                 (main!nl_basics.eq_.? (I temp_62_0~4830@) (I temp_62_1~4845@))
                                                                                                                                                                                                                                                               ))
                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                (main!nl_basics.eq_.? (I temp_62_0~4830@) (I temp_62_1~4845@))
                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                 (= temp_63_0~4892@ (main!nl_basics.mod_.? (I (main!nl_basics.add_.? (I (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                       (I a~2@) (I c~6@)
                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                     ) (I (main!nl_basics.mul_.? (I a~2@) (I b~4@)))
                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                   ) (I m~10@)
                                                                                                                                                                                                                                                                 ))
                                                                                                                                                                                                                                                                 (=>
                                                                                                                                                                                                                                                                  (= temp_63_1~4917@ (main!nl_basics.mod_.? (I (main!nl_basics.add_.? (I (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                        (I a~2@) (I c~6@)
                                                                                                                                                                                                                                                                       )
                                                                                                                                                                                                                                                                      ) (I (main!nl_basics.mul_.? (I b~4@) (I a~2@)))
                                                                                                                                                                                                                                                                     )
                                                                                                                                                                                                                                                                    ) (I m~10@)
                                                                                                                                                                                                                                                                  ))
                                                                                                                                                                                                                                                                  (and
                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                     %%location_label%%63
                                                                                                                                                                                                                                                                     (main!nl_basics.eq_.? (I temp_63_0~4892@) (I temp_63_1~4917@))
                                                                                                                                                                                                                                                                   ))
                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                    (main!nl_basics.eq_.? (I temp_63_0~4892@) (I temp_63_1~4917@))
                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                     (= temp_64_0~4964@ (main!nl_basics.sub_.? (I (main!nl_basics.mul_.? (I b~4@) (I d~8@)))
                                                                                                                                                                                                                                                                       (I (main!nl_basics.mod_.? (I (main!nl_basics.mul_.? (I a~2@) (I d~8@))) (I m~10@)))
                                                                                                                                                                                                                                                                     ))
                                                                                                                                                                                                                                                                     (=>
                                                                                                                                                                                                                                                                      (= temp_64_1~5024@ (main!nl_basics.sub_.? (I (main!nl_basics.mul_.? (I b~4@) (I d~8@)))
                                                                                                                                                                                                                                                                        (I (main!nl_basics.mod_.? (I (main!nl_basics.add_.? (I (main!nl_basics.mul_.? (I a~2@)
                                                                                                                                                                                                                                                                              (I d~8@)
                                                                                                                                                                                                                                                                             )
                                                                                                                                                                                                                                                                            ) (I (main!nl_basics.mul_.? (I (main!nl_basics.mod_.? (I (main!nl_basics.mul_.? (I (main!nl_basics.sub_.?
                                                                                                                                                                                                                                                                                    (I d~8@) (I (main!nl_basics.mod_.? (I a~2@) (I m~10@)))
                                                                                                                                                                                                                                                                                   )
                                                                                                                                                                                                                                                                                  ) (I (main!nl_basics.mul_.? (I a~2@) (I b~4@)))
                                                                                                                                                                                                                                                                                 )
                                                                                                                                                                                                                                                                                ) (I m~10@)
                                                                                                                                                                                                                                                                               )
                                                                                                                                                                                                                                                                              ) (I m~10@)
                                                                                                                                                                                                                                                                           )))
                                                                                                                                                                                                                                                                          ) (I m~10@)
                                                                                                                                                                                                                                                                      ))))
                                                                                                                                                                                                                                                                      (and
                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                         %%location_label%%64
                                                                                                                                                                                                                                                                         (main!nl_basics.eq_.? (I temp_64_0~4964@) (I temp_64_1~5024@))
                                                                                                                                                                                                                                                                       ))
                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                        (main!nl_basics.eq_.? (I temp_64_0~4964@) (I temp_64_1~5024@))
                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                         (= temp_65_0~5066@ (main!nl_basics.mul_.? (I (main!nl_basics.mod_.? (I (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                               (I b~4@) (I c~6@)
                                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                                             ) (I m~10@)
                                                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                                                           ) (I a~2@)
                                                                                                                                                                                                                                                                         ))
                                                                                                                                                                                                                                                                         (=>
                                                                                                                                                                                                                                                                          (= temp_65_1~5086@ (main!nl_basics.mul_.? (I (main!nl_basics.mod_.? (I (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                (I c~6@) (I b~4@)
                                                                                                                                                                                                                                                                               )
                                                                                                                                                                                                                                                                              ) (I m~10@)
                                                                                                                                                                                                                                                                             )
                                                                                                                                                                                                                                                                            ) (I a~2@)
                                                                                                                                                                                                                                                                          ))
                                                                                                                                                                                                                                                                          (and
                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                             %%location_label%%65
                                                                                                                                                                                                                                                                             (main!nl_basics.eq_.? (I temp_65_0~5066@) (I temp_65_1~5086@))
                                                                                                                                                                                                                                                                           ))
                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                            (main!nl_basics.eq_.? (I temp_65_0~5066@) (I temp_65_1~5086@))
                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                             (= temp_66_0~5128@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I d~8@) (I c~6@)))
                                                                                                                                                                                                                                                                               (I (main!nl_basics.mul_.? (I b~4@) (I a~2@)))
                                                                                                                                                                                                                                                                             ))
                                                                                                                                                                                                                                                                             (=>
                                                                                                                                                                                                                                                                              (= temp_66_1~5148@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                    (I d~8@) (I c~6@)
                                                                                                                                                                                                                                                                                   )
                                                                                                                                                                                                                                                                                  ) (I b~4@)
                                                                                                                                                                                                                                                                                 )
                                                                                                                                                                                                                                                                                ) (I a~2@)
                                                                                                                                                                                                                                                                              ))
                                                                                                                                                                                                                                                                              (and
                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                 %%location_label%%66
                                                                                                                                                                                                                                                                                 (main!nl_basics.eq_.? (I temp_66_0~5128@) (I temp_66_1~5148@))
                                                                                                                                                                                                                                                                               ))
                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                (main!nl_basics.eq_.? (I temp_66_0~5128@) (I temp_66_1~5148@))
                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                 (= temp_67_0~5195@ (main!nl_basics.mul_.? (I (main!nl_basics.mod_.? (I (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                       (I c~6@) (I c~6@)
                                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                                     ) (I m~10@)
                                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                                   ) (I (main!nl_basics.mul_.? (I d~8@) (I d~8@)))
                                                                                                                                                                                                                                                                                 ))
                                                                                                                                                                                                                                                                                 (=>
                                                                                                                                                                                                                                                                                  (= temp_67_1~5250@ (main!nl_basics.mul_.? (I (main!nl_basics.mod_.? (I (main!nl_basics.add_.?
                                                                                                                                                                                                                                                                                        (I (main!nl_basics.mul_.? (I (main!nl_basics.mod_.? (I (main!nl_basics.add_.? (I (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                (I a~2@) (I d~8@)
                                                                                                                                                                                                                                                                                               )
                                                                                                                                                                                                                                                                                              ) (I (main!nl_basics.mul_.? (I a~2@) (I a~2@)))
                                                                                                                                                                                                                                                                                             )
                                                                                                                                                                                                                                                                                            ) (I m~10@)
                                                                                                                                                                                                                                                                                           )
                                                                                                                                                                                                                                                                                          ) (I m~10@)
                                                                                                                                                                                                                                                                                         )
                                                                                                                                                                                                                                                                                        ) (I (main!nl_basics.mul_.? (I c~6@) (I c~6@)))
                                                                                                                                                                                                                                                                                       )
                                                                                                                                                                                                                                                                                      ) (I m~10@)
                                                                                                                                                                                                                                                                                     )
                                                                                                                                                                                                                                                                                    ) (I (main!nl_basics.mul_.? (I d~8@) (I d~8@)))
                                                                                                                                                                                                                                                                                  ))
                                                                                                                                                                                                                                                                                  (and
                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                     %%location_label%%67
                                                                                                                                                                                                                                                                                     (main!nl_basics.eq_.? (I temp_67_0~5195@) (I temp_67_1~5250@))
                                                                                                                                                                                                                                                                                   ))
                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                    (main!nl_basics.eq_.? (I temp_67_0~5195@) (I temp_67_1~5250@))
                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                     (= temp_68_0~5297@ (main!nl_basics.mul_.? (I (main!nl_basics.add_.? (I a~2@) (I a~2@)))
                                                                                                                                                                                                                                                                                       (I (main!nl_basics.mod_.? (I (main!nl_basics.mul_.? (I d~8@) (I c~6@))) (I m~10@)))
                                                                                                                                                                                                                                                                                     ))
                                                                                                                                                                                                                                                                                     (=>
                                                                                                                                                                                                                                                                                      (= temp_68_1~5322@ (main!nl_basics.mul_.? (I (main!nl_basics.add_.? (I a~2@) (I a~2@)))
                                                                                                                                                                                                                                                                                        (I (main!nl_basics.mod_.? (I (main!nl_basics.mul_.? (I c~6@) (I d~8@))) (I m~10@)))
                                                                                                                                                                                                                                                                                      ))
                                                                                                                                                                                                                                                                                      (and
                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                         %%location_label%%68
                                                                                                                                                                                                                                                                                         (main!nl_basics.eq_.? (I temp_68_0~5297@) (I temp_68_1~5322@))
                                                                                                                                                                                                                                                                                       ))
                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                        (main!nl_basics.eq_.? (I temp_68_0~5297@) (I temp_68_1~5322@))
                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                         (= temp_69_0~5364@ (main!nl_basics.mul_.? (I (main!nl_basics.mod_.? (I d~8@) (I m~10@)))
                                                                                                                                                                                                                                                                                           (I (main!nl_basics.add_.? (I a~2@) (I b~4@)))
                                                                                                                                                                                                                                                                                         ))
                                                                                                                                                                                                                                                                                         (=>
                                                                                                                                                                                                                                                                                          (= temp_69_1~5394@ (main!nl_basics.add_.? (I (main!nl_basics.mul_.? (I (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                (I d~8@) (I m~10@)
                                                                                                                                                                                                                                                                                               )
                                                                                                                                                                                                                                                                                              ) (I a~2@)
                                                                                                                                                                                                                                                                                             )
                                                                                                                                                                                                                                                                                            ) (I (main!nl_basics.mul_.? (I (main!nl_basics.mod_.? (I d~8@) (I m~10@))) (I b~4@)))
                                                                                                                                                                                                                                                                                          ))
                                                                                                                                                                                                                                                                                          (and
                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                             %%location_label%%69
                                                                                                                                                                                                                                                                                             (main!nl_basics.eq_.? (I temp_69_0~5364@) (I temp_69_1~5394@))
                                                                                                                                                                                                                                                                                           ))
                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                            (main!nl_basics.eq_.? (I temp_69_0~5364@) (I temp_69_1~5394@))
                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                             (= temp_70_0~5436@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I a~2@) (I a~2@)))
                                                                                                                                                                                                                                                                                               (I (main!nl_basics.mul_.? (I a~2@) (I c~6@)))
                                                                                                                                                                                                                                                                                             ))
                                                                                                                                                                                                                                                                                             (=>
                                                                                                                                                                                                                                                                                              (= temp_70_1~5456@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I a~2@) (I c~6@)))
                                                                                                                                                                                                                                                                                                (I (main!nl_basics.mul_.? (I a~2@) (I a~2@)))
                                                                                                                                                                                                                                                                                              ))
                                                                                                                                                                                                                                                                                              (and
                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                 %%location_label%%70
                                                                                                                                                                                                                                                                                                 (main!nl_basics.eq_.? (I temp_70_0~5436@) (I temp_70_1~5456@))
                                                                                                                                                                                                                                                                                               ))
                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                (main!nl_basics.eq_.? (I temp_70_0~5436@) (I temp_70_1~5456@))
                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                 (= temp_71_0~5498@ (main!nl_basics.sub_.? (I (main!nl_basics.mul_.? (I a~2@) (I b~4@)))
                                                                                                                                                                                                                                                                                                   (I (main!nl_basics.mul_.? (I a~2@) (I d~8@)))
                                                                                                                                                                                                                                                                                                 ))
                                                                                                                                                                                                                                                                                                 (=>
                                                                                                                                                                                                                                                                                                  (= temp_71_1~5518@ (main!nl_basics.sub_.? (I (main!nl_basics.mul_.? (I a~2@) (I b~4@)))
                                                                                                                                                                                                                                                                                                    (I (main!nl_basics.mul_.? (I d~8@) (I a~2@)))
                                                                                                                                                                                                                                                                                                  ))
                                                                                                                                                                                                                                                                                                  (and
                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                     %%location_label%%71
                                                                                                                                                                                                                                                                                                     (main!nl_basics.eq_.? (I temp_71_0~5498@) (I temp_71_1~5518@))
                                                                                                                                                                                                                                                                                                   ))
                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                    (main!nl_basics.eq_.? (I temp_71_0~5498@) (I temp_71_1~5518@))
                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                     (= temp_72_0~5575@ (main!nl_basics.mod_.? (I (main!nl_basics.mul_.? (I (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                           (I (main!nl_basics.mod_.? (I a~2@) (I m~10@))) (I (main!nl_basics.mod_.? (I a~2@) (
                                                                                                                                                                                                                                                                                                              I m~10@
                                                                                                                                                                                                                                                                                                          ))))
                                                                                                                                                                                                                                                                                                         ) (I (main!nl_basics.mul_.? (I d~8@) (I b~4@)))
                                                                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                                                                       ) (I m~10@)
                                                                                                                                                                                                                                                                                                     ))
                                                                                                                                                                                                                                                                                                     (=>
                                                                                                                                                                                                                                                                                                      (= temp_72_1~5610@ (main!nl_basics.mod_.? (I (main!nl_basics.mul_.? (I (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                            (I (main!nl_basics.mod_.? (I a~2@) (I m~10@))) (I (main!nl_basics.mod_.? (I a~2@) (
                                                                                                                                                                                                                                                                                                               I m~10@
                                                                                                                                                                                                                                                                                                           ))))
                                                                                                                                                                                                                                                                                                          ) (I (main!nl_basics.mul_.? (I b~4@) (I d~8@)))
                                                                                                                                                                                                                                                                                                         )
                                                                                                                                                                                                                                                                                                        ) (I m~10@)
                                                                                                                                                                                                                                                                                                      ))
                                                                                                                                                                                                                                                                                                      (and
                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                         %%location_label%%72
                                                                                                                                                                                                                                                                                                         (main!nl_basics.eq_.? (I temp_72_0~5575@) (I temp_72_1~5610@))
                                                                                                                                                                                                                                                                                                       ))
                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                        (main!nl_basics.eq_.? (I temp_72_0~5575@) (I temp_72_1~5610@))
                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                         (= temp_73_0~5652@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I a~2@) (I b~4@)))
                                                                                                                                                                                                                                                                                                           (I (main!nl_basics.mul_.? (I d~8@) (I b~4@)))
                                                                                                                                                                                                                                                                                                         ))
                                                                                                                                                                                                                                                                                                         (=>
                                                                                                                                                                                                                                                                                                          (= temp_73_1~5672@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                (I a~2@) (I b~4@)
                                                                                                                                                                                                                                                                                                               )
                                                                                                                                                                                                                                                                                                              ) (I d~8@)
                                                                                                                                                                                                                                                                                                             )
                                                                                                                                                                                                                                                                                                            ) (I b~4@)
                                                                                                                                                                                                                                                                                                          ))
                                                                                                                                                                                                                                                                                                          (and
                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                             %%location_label%%73
                                                                                                                                                                                                                                                                                                             (main!nl_basics.eq_.? (I temp_73_0~5652@) (I temp_73_1~5672@))
                                                                                                                                                                                                                                                                                                           ))
                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                            (main!nl_basics.eq_.? (I temp_73_0~5652@) (I temp_73_1~5672@))
                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                             (= temp_74_0~5724@ (main!nl_basics.mul_.? (I (main!nl_basics.mod_.? (I (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                   (I c~6@) (I c~6@)
                                                                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                                                                 ) (I m~10@)
                                                                                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                                                                               ) (I (main!nl_basics.mod_.? (I (main!nl_basics.add_.? (I d~8@) (I a~2@))) (I m~10@)))
                                                                                                                                                                                                                                                                                                             ))
                                                                                                                                                                                                                                                                                                             (=>
                                                                                                                                                                                                                                                                                                              (= temp_74_1~5754@ (main!nl_basics.mul_.? (I (main!nl_basics.mod_.? (I (main!nl_basics.add_.?
                                                                                                                                                                                                                                                                                                                    (I d~8@) (I a~2@)
                                                                                                                                                                                                                                                                                                                   )
                                                                                                                                                                                                                                                                                                                  ) (I m~10@)
                                                                                                                                                                                                                                                                                                                 )
                                                                                                                                                                                                                                                                                                                ) (I (main!nl_basics.mod_.? (I (main!nl_basics.mul_.? (I c~6@) (I c~6@))) (I m~10@)))
                                                                                                                                                                                                                                                                                                              ))
                                                                                                                                                                                                                                                                                                              (and
                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                 %%location_label%%74
                                                                                                                                                                                                                                                                                                                 (main!nl_basics.eq_.? (I temp_74_0~5724@) (I temp_74_1~5754@))
                                                                                                                                                                                                                                                                                                               ))
                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                (main!nl_basics.eq_.? (I temp_74_0~5724@) (I temp_74_1~5754@))
                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                 (= temp_75_0~5801@ (main!nl_basics.mul_.? (I (main!nl_basics.sub_.? (I d~8@) (I (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                       (I d~8@) (I m~10@)
                                                                                                                                                                                                                                                                                                                    )))
                                                                                                                                                                                                                                                                                                                   ) (I (main!nl_basics.mul_.? (I b~4@) (I c~6@)))
                                                                                                                                                                                                                                                                                                                 ))
                                                                                                                                                                                                                                                                                                                 (=>
                                                                                                                                                                                                                                                                                                                  (= temp_75_1~5856@ (main!nl_basics.mul_.? (I (main!nl_basics.sub_.? (I d~8@) (I (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                        (I (main!nl_basics.sub_.? (I d~8@) (I (main!nl_basics.mul_.? (I (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                              (I (main!nl_basics.mul_.? (I c~6@) (I a~2@))) (I (main!nl_basics.mod_.? (I (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                  (I a~2@) (I d~8@)
                                                                                                                                                                                                                                                                                                                                 )
                                                                                                                                                                                                                                                                                                                                ) (I m~10@)
                                                                                                                                                                                                                                                                                                                             )))
                                                                                                                                                                                                                                                                                                                            ) (I m~10@)
                                                                                                                                                                                                                                                                                                                         )))
                                                                                                                                                                                                                                                                                                                        ) (I m~10@)
                                                                                                                                                                                                                                                                                                                     )))
                                                                                                                                                                                                                                                                                                                    ) (I (main!nl_basics.mul_.? (I b~4@) (I c~6@)))
                                                                                                                                                                                                                                                                                                                  ))
                                                                                                                                                                                                                                                                                                                  (and
                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                     %%location_label%%75
                                                                                                                                                                                                                                                                                                                     (main!nl_basics.eq_.? (I temp_75_0~5801@) (I temp_75_1~5856@))
                                                                                                                                                                                                                                                                                                                   ))
                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                    (main!nl_basics.eq_.? (I temp_75_0~5801@) (I temp_75_1~5856@))
                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                     (= temp_76_0~5908@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I c~6@) (I (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                           (I b~4@) (I m~10@)
                                                                                                                                                                                                                                                                                                                        )))
                                                                                                                                                                                                                                                                                                                       ) (I (main!nl_basics.mul_.? (I (main!nl_basics.mod_.? (I b~4@) (I m~10@))) (I d~8@)))
                                                                                                                                                                                                                                                                                                                     ))
                                                                                                                                                                                                                                                                                                                     (=>
                                                                                                                                                                                                                                                                                                                      (= temp_76_1~5938@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                            (I c~6@) (I (main!nl_basics.mod_.? (I b~4@) (I m~10@)))
                                                                                                                                                                                                                                                                                                                           )
                                                                                                                                                                                                                                                                                                                          ) (I (main!nl_basics.mod_.? (I b~4@) (I m~10@)))
                                                                                                                                                                                                                                                                                                                         )
                                                                                                                                                                                                                                                                                                                        ) (I d~8@)
                                                                                                                                                                                                                                                                                                                      ))
                                                                                                                                                                                                                                                                                                                      (and
                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                         %%location_label%%76
                                                                                                                                                                                                                                                                                                                         (main!nl_basics.eq_.? (I temp_76_0~5908@) (I temp_76_1~5938@))
                                                                                                                                                                                                                                                                                                                       ))
                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                        (main!nl_basics.eq_.? (I temp_76_0~5908@) (I temp_76_1~5938@))
                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                         (= temp_77_0~5980@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I c~6@) (I a~2@)))
                                                                                                                                                                                                                                                                                                                           (I (main!nl_basics.mul_.? (I a~2@) (I a~2@)))
                                                                                                                                                                                                                                                                                                                         ))
                                                                                                                                                                                                                                                                                                                         (=>
                                                                                                                                                                                                                                                                                                                          (= temp_77_1~6000@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I c~6@) (I a~2@)))
                                                                                                                                                                                                                                                                                                                            (I (main!nl_basics.mul_.? (I a~2@) (I a~2@)))
                                                                                                                                                                                                                                                                                                                          ))
                                                                                                                                                                                                                                                                                                                          (and
                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                                             %%location_label%%77
                                                                                                                                                                                                                                                                                                                             (main!nl_basics.eq_.? (I temp_77_0~5980@) (I temp_77_1~6000@))
                                                                                                                                                                                                                                                                                                                           ))
                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                            (main!nl_basics.eq_.? (I temp_77_0~5980@) (I temp_77_1~6000@))
                                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                                             (= temp_78_0~6042@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I b~4@) (I a~2@)))
                                                                                                                                                                                                                                                                                                                               (I (main!nl_basics.mul_.? (I b~4@) (I c~6@)))
                                                                                                                                                                                                                                                                                                                             ))
                                                                                                                                                                                                                                                                                                                             (=>
                                                                                                                                                                                                                                                                                                                              (= temp_78_1~6062@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I a~2@) (I b~4@)))
                                                                                                                                                                                                                                                                                                                                (I (main!nl_basics.mul_.? (I b~4@) (I c~6@)))
                                                                                                                                                                                                                                                                                                                              ))
                                                                                                                                                                                                                                                                                                                              (and
                                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                                 %%location_label%%78
                                                                                                                                                                                                                                                                                                                                 (main!nl_basics.eq_.? (I temp_78_0~6042@) (I temp_78_1~6062@))
                                                                                                                                                                                                                                                                                                                               ))
                                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                                (main!nl_basics.eq_.? (I temp_78_0~6042@) (I temp_78_1~6062@))
                                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                                 (= temp_79_0~6114@ (main!nl_basics.mod_.? (I (main!nl_basics.mul_.? (I (main!nl_basics.add_.?
                                                                                                                                                                                                                                                                                                                                       (I b~4@) (I a~2@)
                                                                                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                                                                                     ) (I (main!nl_basics.mul_.? (I (main!nl_basics.mod_.? (I a~2@) (I m~10@))) (I d~8@)))
                                                                                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                                                                                   ) (I m~10@)
                                                                                                                                                                                                                                                                                                                                 ))
                                                                                                                                                                                                                                                                                                                                 (=>
                                                                                                                                                                                                                                                                                                                                  (= temp_79_1~6159@ (main!nl_basics.mod_.? (I (main!nl_basics.add_.? (I (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                        (I b~4@) (I (main!nl_basics.mul_.? (I (main!nl_basics.mod_.? (I a~2@) (I m~10@))) (
                                                                                                                                                                                                                                                                                                                                           I d~8@
                                                                                                                                                                                                                                                                                                                                       ))))
                                                                                                                                                                                                                                                                                                                                      ) (I (main!nl_basics.mul_.? (I a~2@) (I (main!nl_basics.mul_.? (I (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                            (I a~2@) (I m~10@)
                                                                                                                                                                                                                                                                                                                                           )
                                                                                                                                                                                                                                                                                                                                          ) (I d~8@)
                                                                                                                                                                                                                                                                                                                                     )))))
                                                                                                                                                                                                                                                                                                                                    ) (I m~10@)
                                                                                                                                                                                                                                                                                                                                  ))
                                                                                                                                                                                                                                                                                                                                  (and
                                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                                     %%location_label%%79
                                                                                                                                                                                                                                                                                                                                     (main!nl_basics.eq_.? (I temp_79_0~6114@) (I temp_79_1~6159@))
                                                                                                                                                                                                                                                                                                                                   ))
                                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                                    (main!nl_basics.eq_.? (I temp_79_0~6114@) (I temp_79_1~6159@))
                                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                                     (= temp_80_0~6206@ (main!nl_basics.sub_.? (I (main!nl_basics.mod_.? (I (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                           (I a~2@) (I d~8@)
                                                                                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                                                                                         ) (I m~10@)
                                                                                                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                                                                                                       ) (I (main!nl_basics.mul_.? (I a~2@) (I d~8@)))
                                                                                                                                                                                                                                                                                                                                     ))
                                                                                                                                                                                                                                                                                                                                     (=>
                                                                                                                                                                                                                                                                                                                                      (= temp_80_1~6261@ (main!nl_basics.sub_.? (I (main!nl_basics.mod_.? (I (main!nl_basics.sub_.?
                                                                                                                                                                                                                                                                                                                                            (I (main!nl_basics.mul_.? (I a~2@) (I d~8@))) (I (main!nl_basics.mul_.? (I (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                (I (main!nl_basics.add_.? (I (main!nl_basics.mul_.? (I d~8@) (I a~2@))) (I (main!nl_basics.sub_.?
                                                                                                                                                                                                                                                                                                                                                    (I d~8@) (I c~6@)
                                                                                                                                                                                                                                                                                                                                                 )))
                                                                                                                                                                                                                                                                                                                                                ) (I m~10@)
                                                                                                                                                                                                                                                                                                                                               )
                                                                                                                                                                                                                                                                                                                                              ) (I m~10@)
                                                                                                                                                                                                                                                                                                                                           )))
                                                                                                                                                                                                                                                                                                                                          ) (I m~10@)
                                                                                                                                                                                                                                                                                                                                         )
                                                                                                                                                                                                                                                                                                                                        ) (I (main!nl_basics.mul_.? (I a~2@) (I d~8@)))
                                                                                                                                                                                                                                                                                                                                      ))
                                                                                                                                                                                                                                                                                                                                      (and
                                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                                         %%location_label%%80
                                                                                                                                                                                                                                                                                                                                         (main!nl_basics.eq_.? (I temp_80_0~6206@) (I temp_80_1~6261@))
                                                                                                                                                                                                                                                                                                                                       ))
                                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                                        (main!nl_basics.eq_.? (I temp_80_0~6206@) (I temp_80_1~6261@))
                                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                                         (= temp_81_0~6303@ (main!nl_basics.mul_.? (I (main!nl_basics.add_.? (I b~4@) (I c~6@)))
                                                                                                                                                                                                                                                                                                                                           (I (main!nl_basics.mul_.? (I a~2@) (I a~2@)))
                                                                                                                                                                                                                                                                                                                                         ))
                                                                                                                                                                                                                                                                                                                                         (=>
                                                                                                                                                                                                                                                                                                                                          (= temp_81_1~6323@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I (main!nl_basics.add_.?
                                                                                                                                                                                                                                                                                                                                                (I b~4@) (I c~6@)
                                                                                                                                                                                                                                                                                                                                               )
                                                                                                                                                                                                                                                                                                                                              ) (I a~2@)
                                                                                                                                                                                                                                                                                                                                             )
                                                                                                                                                                                                                                                                                                                                            ) (I a~2@)
                                                                                                                                                                                                                                                                                                                                          ))
                                                                                                                                                                                                                                                                                                                                          (and
                                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                                                             %%location_label%%81
                                                                                                                                                                                                                                                                                                                                             (main!nl_basics.eq_.? (I temp_81_0~6303@) (I temp_81_1~6323@))
                                                                                                                                                                                                                                                                                                                                           ))
                                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                                            (main!nl_basics.eq_.? (I temp_81_0~6303@) (I temp_81_1~6323@))
                                                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                                                             (= temp_82_0~6365@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I c~6@) (I c~6@)))
                                                                                                                                                                                                                                                                                                                                               (I (main!nl_basics.mul_.? (I a~2@) (I a~2@)))
                                                                                                                                                                                                                                                                                                                                             ))
                                                                                                                                                                                                                                                                                                                                             (=>
                                                                                                                                                                                                                                                                                                                                              (= temp_82_1~6385@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I c~6@) (I c~6@)))
                                                                                                                                                                                                                                                                                                                                                (I (main!nl_basics.mul_.? (I a~2@) (I a~2@)))
                                                                                                                                                                                                                                                                                                                                              ))
                                                                                                                                                                                                                                                                                                                                              (and
                                                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                                                 %%location_label%%82
                                                                                                                                                                                                                                                                                                                                                 (main!nl_basics.eq_.? (I temp_82_0~6365@) (I temp_82_1~6385@))
                                                                                                                                                                                                                                                                                                                                               ))
                                                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                                                (main!nl_basics.eq_.? (I temp_82_0~6365@) (I temp_82_1~6385@))
                                                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                                                 (= temp_83_0~6427@ (main!nl_basics.mul_.? (I (main!nl_basics.add_.? (I c~6@) (I b~4@)))
                                                                                                                                                                                                                                                                                                                                                   (I (main!nl_basics.mul_.? (I d~8@) (I d~8@)))
                                                                                                                                                                                                                                                                                                                                                 ))
                                                                                                                                                                                                                                                                                                                                                 (=>
                                                                                                                                                                                                                                                                                                                                                  (= temp_83_1~6447@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I d~8@) (I d~8@)))
                                                                                                                                                                                                                                                                                                                                                    (I (main!nl_basics.add_.? (I c~6@) (I b~4@)))
                                                                                                                                                                                                                                                                                                                                                  ))
                                                                                                                                                                                                                                                                                                                                                  (and
                                                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                                                     %%location_label%%83
                                                                                                                                                                                                                                                                                                                                                     (main!nl_basics.eq_.? (I temp_83_0~6427@) (I temp_83_1~6447@))
                                                                                                                                                                                                                                                                                                                                                   ))
                                                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                                                    (main!nl_basics.eq_.? (I temp_83_0~6427@) (I temp_83_1~6447@))
                                                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                                                     (= temp_84_0~6489@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I c~6@) (I a~2@)))
                                                                                                                                                                                                                                                                                                                                                       (I (main!nl_basics.mul_.? (I b~4@) (I b~4@)))
                                                                                                                                                                                                                                                                                                                                                     ))
                                                                                                                                                                                                                                                                                                                                                     (=>
                                                                                                                                                                                                                                                                                                                                                      (= temp_84_1~6509@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I a~2@) (I c~6@)))
                                                                                                                                                                                                                                                                                                                                                        (I (main!nl_basics.mul_.? (I b~4@) (I b~4@)))
                                                                                                                                                                                                                                                                                                                                                      ))
                                                                                                                                                                                                                                                                                                                                                      (and
                                                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                                                         %%location_label%%84
                                                                                                                                                                                                                                                                                                                                                         (main!nl_basics.eq_.? (I temp_84_0~6489@) (I temp_84_1~6509@))
                                                                                                                                                                                                                                                                                                                                                       ))
                                                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                                                        (main!nl_basics.eq_.? (I temp_84_0~6489@) (I temp_84_1~6509@))
                                                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                                                         (= temp_85_0~6556@ (main!nl_basics.add_.? (I (main!nl_basics.add_.? (I b~4@) (I a~2@)))
                                                                                                                                                                                                                                                                                                                                                           (I (main!nl_basics.mod_.? (I (main!nl_basics.mul_.? (I d~8@) (I a~2@))) (I m~10@)))
                                                                                                                                                                                                                                                                                                                                                         ))
                                                                                                                                                                                                                                                                                                                                                         (=>
                                                                                                                                                                                                                                                                                                                                                          (= temp_85_1~6581@ (main!nl_basics.add_.? (I (main!nl_basics.mod_.? (I (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                (I d~8@) (I a~2@)
                                                                                                                                                                                                                                                                                                                                                               )
                                                                                                                                                                                                                                                                                                                                                              ) (I m~10@)
                                                                                                                                                                                                                                                                                                                                                             )
                                                                                                                                                                                                                                                                                                                                                            ) (I (main!nl_basics.add_.? (I b~4@) (I a~2@)))
                                                                                                                                                                                                                                                                                                                                                          ))
                                                                                                                                                                                                                                                                                                                                                          (and
                                                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                                                                             %%location_label%%85
                                                                                                                                                                                                                                                                                                                                                             (main!nl_basics.eq_.? (I temp_85_0~6556@) (I temp_85_1~6581@))
                                                                                                                                                                                                                                                                                                                                                           ))
                                                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                                                            (main!nl_basics.eq_.? (I temp_85_0~6556@) (I temp_85_1~6581@))
                                                                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                                                                             (= temp_86_0~6623@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I b~4@) (I c~6@)))
                                                                                                                                                                                                                                                                                                                                                               (I (main!nl_basics.mul_.? (I b~4@) (I c~6@)))
                                                                                                                                                                                                                                                                                                                                                             ))
                                                                                                                                                                                                                                                                                                                                                             (=>
                                                                                                                                                                                                                                                                                                                                                              (= temp_86_1~6643@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I c~6@) (I b~4@)))
                                                                                                                                                                                                                                                                                                                                                                (I (main!nl_basics.mul_.? (I b~4@) (I c~6@)))
                                                                                                                                                                                                                                                                                                                                                              ))
                                                                                                                                                                                                                                                                                                                                                              (and
                                                                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                                                                 %%location_label%%86
                                                                                                                                                                                                                                                                                                                                                                 (main!nl_basics.eq_.? (I temp_86_0~6623@) (I temp_86_1~6643@))
                                                                                                                                                                                                                                                                                                                                                               ))
                                                                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                                                                (main!nl_basics.eq_.? (I temp_86_0~6623@) (I temp_86_1~6643@))
                                                                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                                                                 (= temp_87_0~6685@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I d~8@) (I c~6@)))
                                                                                                                                                                                                                                                                                                                                                                   (I (main!nl_basics.mul_.? (I c~6@) (I d~8@)))
                                                                                                                                                                                                                                                                                                                                                                 ))
                                                                                                                                                                                                                                                                                                                                                                 (=>
                                                                                                                                                                                                                                                                                                                                                                  (= temp_87_1~6705@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I c~6@) (I d~8@)))
                                                                                                                                                                                                                                                                                                                                                                    (I (main!nl_basics.mul_.? (I d~8@) (I c~6@)))
                                                                                                                                                                                                                                                                                                                                                                  ))
                                                                                                                                                                                                                                                                                                                                                                  (and
                                                                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                                                                     %%location_label%%87
                                                                                                                                                                                                                                                                                                                                                                     (main!nl_basics.eq_.? (I temp_87_0~6685@) (I temp_87_1~6705@))
                                                                                                                                                                                                                                                                                                                                                                   ))
                                                                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                                                                    (main!nl_basics.eq_.? (I temp_87_0~6685@) (I temp_87_1~6705@))
                                                                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                                                                     (= temp_88_0~6747@ (main!nl_basics.add_.? (I (main!nl_basics.sub_.? (I d~8@) (I a~2@)))
                                                                                                                                                                                                                                                                                                                                                                       (I (main!nl_basics.mul_.? (I c~6@) (I c~6@)))
                                                                                                                                                                                                                                                                                                                                                                     ))
                                                                                                                                                                                                                                                                                                                                                                     (=>
                                                                                                                                                                                                                                                                                                                                                                      (= temp_88_1~6767@ (main!nl_basics.add_.? (I (main!nl_basics.mul_.? (I c~6@) (I c~6@)))
                                                                                                                                                                                                                                                                                                                                                                        (I (main!nl_basics.sub_.? (I d~8@) (I a~2@)))
                                                                                                                                                                                                                                                                                                                                                                      ))
                                                                                                                                                                                                                                                                                                                                                                      (and
                                                                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                                                                         %%location_label%%88
                                                                                                                                                                                                                                                                                                                                                                         (main!nl_basics.eq_.? (I temp_88_0~6747@) (I temp_88_1~6767@))
                                                                                                                                                                                                                                                                                                                                                                       ))
                                                                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                                                                        (main!nl_basics.eq_.? (I temp_88_0~6747@) (I temp_88_1~6767@))
                                                                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                                                                         (= temp_89_0~6819@ (main!nl_basics.sub_.? (I (main!nl_basics.mul_.? (I b~4@) (I (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                                               (I b~4@) (I m~10@)
                                                                                                                                                                                                                                                                                                                                                                            )))
                                                                                                                                                                                                                                                                                                                                                                           ) (I (main!nl_basics.mul_.? (I b~4@) (I (main!nl_basics.mod_.? (I c~6@) (I m~10@)))))
                                                                                                                                                                                                                                                                                                                                                                         ))
                                                                                                                                                                                                                                                                                                                                                                         (=>
                                                                                                                                                                                                                                                                                                                                                                          (= temp_89_1~6849@ (main!nl_basics.sub_.? (I (main!nl_basics.mul_.? (I b~4@) (I (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                                                (I b~4@) (I m~10@)
                                                                                                                                                                                                                                                                                                                                                                             )))
                                                                                                                                                                                                                                                                                                                                                                            ) (I (main!nl_basics.mul_.? (I (main!nl_basics.mod_.? (I c~6@) (I m~10@))) (I b~4@)))
                                                                                                                                                                                                                                                                                                                                                                          ))
                                                                                                                                                                                                                                                                                                                                                                          (and
                                                                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                                                                                             %%location_label%%89
                                                                                                                                                                                                                                                                                                                                                                             (main!nl_basics.eq_.? (I temp_89_0~6819@) (I temp_89_1~6849@))
                                                                                                                                                                                                                                                                                                                                                                           ))
                                                                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                                                                            (main!nl_basics.eq_.? (I temp_89_0~6819@) (I temp_89_1~6849@))
                                                                                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                                                                                             (= temp_90_0~6896@ (main!nl_basics.sub_.? (I (main!nl_basics.mul_.? (I b~4@) (I (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                                                   (I a~2@) (I m~10@)
                                                                                                                                                                                                                                                                                                                                                                                )))
                                                                                                                                                                                                                                                                                                                                                                               ) (I (main!nl_basics.mul_.? (I a~2@) (I b~4@)))
                                                                                                                                                                                                                                                                                                                                                                             ))
                                                                                                                                                                                                                                                                                                                                                                             (=>
                                                                                                                                                                                                                                                                                                                                                                              (= temp_90_1~6951@ (main!nl_basics.sub_.? (I (main!nl_basics.mul_.? (I b~4@) (I (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                                                    (I (main!nl_basics.add_.? (I (main!nl_basics.mul_.? (I (main!nl_basics.mod_.? (I (main!nl_basics.sub_.?
                                                                                                                                                                                                                                                                                                                                                                                            (I (main!nl_basics.mul_.? (I d~8@) (I c~6@))) (I (main!nl_basics.mul_.? (I a~2@) (I
                                                                                                                                                                                                                                                                                                                                                                                               c~6@
                                                                                                                                                                                                                                                                                                                                                                                           ))))
                                                                                                                                                                                                                                                                                                                                                                                          ) (I m~10@)
                                                                                                                                                                                                                                                                                                                                                                                         )
                                                                                                                                                                                                                                                                                                                                                                                        ) (I m~10@)
                                                                                                                                                                                                                                                                                                                                                                                       )
                                                                                                                                                                                                                                                                                                                                                                                      ) (I a~2@)
                                                                                                                                                                                                                                                                                                                                                                                     )
                                                                                                                                                                                                                                                                                                                                                                                    ) (I m~10@)
                                                                                                                                                                                                                                                                                                                                                                                 )))
                                                                                                                                                                                                                                                                                                                                                                                ) (I (main!nl_basics.mul_.? (I a~2@) (I b~4@)))
                                                                                                                                                                                                                                                                                                                                                                              ))
                                                                                                                                                                                                                                                                                                                                                                              (and
                                                                                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                                                                                 %%location_label%%90
                                                                                                                                                                                                                                                                                                                                                                                 (main!nl_basics.eq_.? (I temp_90_0~6896@) (I temp_90_1~6951@))
                                                                                                                                                                                                                                                                                                                                                                               ))
                                                                                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                                                                                (main!nl_basics.eq_.? (I temp_90_0~6896@) (I temp_90_1~6951@))
                                                                                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                                                                                 (= temp_91_0~6993@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I c~6@) (I a~2@)))
                                                                                                                                                                                                                                                                                                                                                                                   (I (main!nl_basics.sub_.? (I d~8@) (I c~6@)))
                                                                                                                                                                                                                                                                                                                                                                                 ))
                                                                                                                                                                                                                                                                                                                                                                                 (=>
                                                                                                                                                                                                                                                                                                                                                                                  (= temp_91_1~7013@ (main!nl_basics.mul_.? (I c~6@) (I (main!nl_basics.mul_.? (I a~2@)
                                                                                                                                                                                                                                                                                                                                                                                      (I (main!nl_basics.sub_.? (I d~8@) (I c~6@)))
                                                                                                                                                                                                                                                                                                                                                                                  ))))
                                                                                                                                                                                                                                                                                                                                                                                  (and
                                                                                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                                                                                     %%location_label%%91
                                                                                                                                                                                                                                                                                                                                                                                     (main!nl_basics.eq_.? (I temp_91_0~6993@) (I temp_91_1~7013@))
                                                                                                                                                                                                                                                                                                                                                                                   ))
                                                                                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                                                                                    (main!nl_basics.eq_.? (I temp_91_0~6993@) (I temp_91_1~7013@))
                                                                                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                                                                                     (= temp_92_0~7065@ (main!nl_basics.mod_.? (I (main!nl_basics.mul_.? (I (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                           (I c~6@) (I c~6@)
                                                                                                                                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                                                                                                                                         ) (I (main!nl_basics.mul_.? (I (main!nl_basics.mod_.? (I b~4@) (I m~10@))) (I b~4@)))
                                                                                                                                                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                                                                                                                                                       ) (I m~10@)
                                                                                                                                                                                                                                                                                                                                                                                     ))
                                                                                                                                                                                                                                                                                                                                                                                     (=>
                                                                                                                                                                                                                                                                                                                                                                                      (= temp_92_1~7125@ (main!nl_basics.mod_.? (I (main!nl_basics.mul_.? (I (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                            (I c~6@) (I c~6@)
                                                                                                                                                                                                                                                                                                                                                                                           )
                                                                                                                                                                                                                                                                                                                                                                                          ) (I (main!nl_basics.mul_.? (I (main!nl_basics.mod_.? (I (main!nl_basics.sub_.? (I b~4@)
                                                                                                                                                                                                                                                                                                                                                                                                (I (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I b~4@)
                                                                                                                                                                                                                                                                                                                                                                                                      (I d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                     )
                                                                                                                                                                                                                                                                                                                                                                                                    ) (I (main!nl_basics.mul_.? (I (main!nl_basics.mod_.? (I a~2@) (I m~10@))) (I a~2@)))
                                                                                                                                                                                                                                                                                                                                                                                                   )
                                                                                                                                                                                                                                                                                                                                                                                                  ) (I m~10@)
                                                                                                                                                                                                                                                                                                                                                                                               )))
                                                                                                                                                                                                                                                                                                                                                                                              ) (I m~10@)
                                                                                                                                                                                                                                                                                                                                                                                             )
                                                                                                                                                                                                                                                                                                                                                                                            ) (I b~4@)
                                                                                                                                                                                                                                                                                                                                                                                         )))
                                                                                                                                                                                                                                                                                                                                                                                        ) (I m~10@)
                                                                                                                                                                                                                                                                                                                                                                                      ))
                                                                                                                                                                                                                                                                                                                                                                                      (and
                                                                                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                                                                                         %%location_label%%92
                                                                                                                                                                                                                                                                                                                                                                                         (main!nl_basics.eq_.? (I temp_92_0~7065@) (I temp_92_1~7125@))
                                                                                                                                                                                                                                                                                                                                                                                       ))
                                                                                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                                                                                        (main!nl_basics.eq_.? (I temp_92_0~7065@) (I temp_92_1~7125@))
                                                                                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                                                                                         (= temp_93_0~7172@ (main!nl_basics.mod_.? (I (main!nl_basics.add_.? (I (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                               (I c~6@) (I c~6@)
                                                                                                                                                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                                                                                                                                                             ) (I (main!nl_basics.add_.? (I b~4@) (I c~6@)))
                                                                                                                                                                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                                                                                                                                                                           ) (I m~10@)
                                                                                                                                                                                                                                                                                                                                                                                         ))
                                                                                                                                                                                                                                                                                                                                                                                         (=>
                                                                                                                                                                                                                                                                                                                                                                                          (= temp_93_1~7227@ (main!nl_basics.mod_.? (I (main!nl_basics.sub_.? (I (main!nl_basics.add_.?
                                                                                                                                                                                                                                                                                                                                                                                                (I (main!nl_basics.mul_.? (I c~6@) (I c~6@))) (I (main!nl_basics.add_.? (I b~4@) (I
                                                                                                                                                                                                                                                                                                                                                                                                   c~6@
                                                                                                                                                                                                                                                                                                                                                                                               ))))
                                                                                                                                                                                                                                                                                                                                                                                              ) (I (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I b~4@)
                                                                                                                                                                                                                                                                                                                                                                                                    (I (main!nl_basics.mod_.? (I c~6@) (I m~10@)))
                                                                                                                                                                                                                                                                                                                                                                                                   )
                                                                                                                                                                                                                                                                                                                                                                                                  ) (I (main!nl_basics.mul_.? (I c~6@) (I a~2@)))
                                                                                                                                                                                                                                                                                                                                                                                                 )
                                                                                                                                                                                                                                                                                                                                                                                                ) (I m~10@)
                                                                                                                                                                                                                                                                                                                                                                                             )))
                                                                                                                                                                                                                                                                                                                                                                                            ) (I m~10@)
                                                                                                                                                                                                                                                                                                                                                                                          ))
                                                                                                                                                                                                                                                                                                                                                                                          (and
                                                                                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                                                                                                             %%location_label%%93
                                                                                                                                                                                                                                                                                                                                                                                             (main!nl_basics.eq_.? (I temp_93_0~7172@) (I temp_93_1~7227@))
                                                                                                                                                                                                                                                                                                                                                                                           ))
                                                                                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                                                                                            (main!nl_basics.eq_.? (I temp_93_0~7172@) (I temp_93_1~7227@))
                                                                                                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                                                                                                             (= temp_94_0~7269@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I a~2@) (I c~6@)))
                                                                                                                                                                                                                                                                                                                                                                                               (I (main!nl_basics.mul_.? (I a~2@) (I c~6@)))
                                                                                                                                                                                                                                                                                                                                                                                             ))
                                                                                                                                                                                                                                                                                                                                                                                             (=>
                                                                                                                                                                                                                                                                                                                                                                                              (= temp_94_1~7289@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I a~2@) (I c~6@)))
                                                                                                                                                                                                                                                                                                                                                                                                (I (main!nl_basics.mul_.? (I a~2@) (I c~6@)))
                                                                                                                                                                                                                                                                                                                                                                                              ))
                                                                                                                                                                                                                                                                                                                                                                                              (and
                                                                                                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                                                                                                 %%location_label%%94
                                                                                                                                                                                                                                                                                                                                                                                                 (main!nl_basics.eq_.? (I temp_94_0~7269@) (I temp_94_1~7289@))
                                                                                                                                                                                                                                                                                                                                                                                               ))
                                                                                                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                                                                                                (main!nl_basics.eq_.? (I temp_94_0~7269@) (I temp_94_1~7289@))
                                                                                                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                                                                                                 (= temp_95_0~7336@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I b~4@) (I (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                                                                       (I d~8@) (I m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                    )))
                                                                                                                                                                                                                                                                                                                                                                                                   ) (I (main!nl_basics.mul_.? (I a~2@) (I b~4@)))
                                                                                                                                                                                                                                                                                                                                                                                                 ))
                                                                                                                                                                                                                                                                                                                                                                                                 (=>
                                                                                                                                                                                                                                                                                                                                                                                                  (= temp_95_1~7361@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I a~2@) (I b~4@)))
                                                                                                                                                                                                                                                                                                                                                                                                    (I (main!nl_basics.mul_.? (I b~4@) (I (main!nl_basics.mod_.? (I d~8@) (I m~10@)))))
                                                                                                                                                                                                                                                                                                                                                                                                  ))
                                                                                                                                                                                                                                                                                                                                                                                                  (and
                                                                                                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                                                                                                     %%location_label%%95
                                                                                                                                                                                                                                                                                                                                                                                                     (main!nl_basics.eq_.? (I temp_95_0~7336@) (I temp_95_1~7361@))
                                                                                                                                                                                                                                                                                                                                                                                                   ))
                                                                                                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                                                                                                    (main!nl_basics.eq_.? (I temp_95_0~7336@) (I temp_95_1~7361@))
                                                                                                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                                                                                                     (= temp_96_0~7415@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I d~8@) (I 38)))
                                                                                                                                                                                                                                                                                                                                                                                                       (I (main!nl_basics.sub_.? (I b~4@) (I d~8@)))
                                                                                                                                                                                                                                                                                                                                                                                                     ))
                                                                                                                                                                                                                                                                                                                                                                                                     (=>
                                                                                                                                                                                                                                                                                                                                                                                                      (= temp_96_1~7447@ (main!nl_basics.mul_.? (I d~8@) (I (main!nl_basics.mul_.? (I 38) (
                                                                                                                                                                                                                                                                                                                                                                                                           I (main!nl_basics.sub_.? (I b~4@) (I d~8@))
                                                                                                                                                                                                                                                                                                                                                                                                      )))))
                                                                                                                                                                                                                                                                                                                                                                                                      (and
                                                                                                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                                                                                                         %%location_label%%96
                                                                                                                                                                                                                                                                                                                                                                                                         (main!nl_basics.eq_.? (I temp_96_0~7415@) (I temp_96_1~7447@))
                                                                                                                                                                                                                                                                                                                                                                                                       ))
                                                                                                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                                                                                                        (main!nl_basics.eq_.? (I temp_96_0~7415@) (I temp_96_1~7447@))
                                                                                                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                                                                                                         (= temp_97_0~7494@ (main!nl_basics.mul_.? (I (main!nl_basics.mod_.? (I (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                               (I d~8@) (I d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                                                                                                                                                                             ) (I m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                                                                                                                                                                                           ) (I (main!nl_basics.mul_.? (I c~6@) (I a~2@)))
                                                                                                                                                                                                                                                                                                                                                                                                         ))
                                                                                                                                                                                                                                                                                                                                                                                                         (=>
                                                                                                                                                                                                                                                                                                                                                                                                          (= temp_97_1~7519@ (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I c~6@) (I a~2@)))
                                                                                                                                                                                                                                                                                                                                                                                                            (I (main!nl_basics.mod_.? (I (main!nl_basics.mul_.? (I d~8@) (I d~8@))) (I m~10@)))
                                                                                                                                                                                                                                                                                                                                                                                                          ))
                                                                                                                                                                                                                                                                                                                                                                                                          (and
                                                                                                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                                                                                                                             %%location_label%%97
                                                                                                                                                                                                                                                                                                                                                                                                             (main!nl_basics.eq_.? (I temp_97_0~7494@) (I temp_97_1~7519@))
                                                                                                                                                                                                                                                                                                                                                                                                           ))
                                                                                                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                                                                                                            (main!nl_basics.eq_.? (I temp_97_0~7494@) (I temp_97_1~7519@))
                                                                                                                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                                                                                                                             (= temp_98_0~7566@ (main!nl_basics.add_.? (I (main!nl_basics.add_.? (I a~2@) (I (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                                                                                   (I a~2@) (I m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                                )))
                                                                                                                                                                                                                                                                                                                                                                                                               ) (I (main!nl_basics.add_.? (I b~4@) (I c~6@)))
                                                                                                                                                                                                                                                                                                                                                                                                             ))
                                                                                                                                                                                                                                                                                                                                                                                                             (=>
                                                                                                                                                                                                                                                                                                                                                                                                              (= temp_98_1~7621@ (main!nl_basics.add_.? (I (main!nl_basics.add_.? (I a~2@) (I (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                                                                                    (I (main!nl_basics.add_.? (I (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I (main!nl_basics.sub_.?
                                                                                                                                                                                                                                                                                                                                                                                                                            (I a~2@) (I b~4@)
                                                                                                                                                                                                                                                                                                                                                                                                                           )
                                                                                                                                                                                                                                                                                                                                                                                                                          ) (I (main!nl_basics.mod_.? (I (main!nl_basics.mul_.? (I c~6@) (I d~8@))) (I m~10@)))
                                                                                                                                                                                                                                                                                                                                                                                                                         )
                                                                                                                                                                                                                                                                                                                                                                                                                        ) (I m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                                       )
                                                                                                                                                                                                                                                                                                                                                                                                                      ) (I a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                                     )
                                                                                                                                                                                                                                                                                                                                                                                                                    ) (I m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                                 )))
                                                                                                                                                                                                                                                                                                                                                                                                                ) (I (main!nl_basics.add_.? (I b~4@) (I c~6@)))
                                                                                                                                                                                                                                                                                                                                                                                                              ))
                                                                                                                                                                                                                                                                                                                                                                                                              (and
                                                                                                                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                                                                                                                 %%location_label%%98
                                                                                                                                                                                                                                                                                                                                                                                                                 (main!nl_basics.eq_.? (I temp_98_0~7566@) (I temp_98_1~7621@))
                                                                                                                                                                                                                                                                                                                                                                                                               ))
                                                                                                                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                                                                                                                (main!nl_basics.eq_.? (I temp_98_0~7566@) (I temp_98_1~7621@))
                                                                                                                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                                                                                                                 (= temp_99_0~7673@ (main!nl_basics.mod_.? (I (main!nl_basics.mul_.? (I (main!nl_basics.add_.?
                                                                                                                                                                                                                                                                                                                                                                                                                       (I a~2@) (I c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                                                                                                                                                                     ) (I (main!nl_basics.mod_.? (I (main!nl_basics.mul_.? (I d~8@) (I c~6@))) (I m~10@)))
                                                                                                                                                                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                                                                                                                                                                   ) (I m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                                 ))
                                                                                                                                                                                                                                                                                                                                                                                                                 (=>
                                                                                                                                                                                                                                                                                                                                                                                                                  (= temp_99_1~7733@ (main!nl_basics.mod_.? (I (main!nl_basics.mul_.? (I (main!nl_basics.add_.?
                                                                                                                                                                                                                                                                                                                                                                                                                        (I a~2@) (I c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                                       )
                                                                                                                                                                                                                                                                                                                                                                                                                      ) (I (main!nl_basics.mod_.? (I (main!nl_basics.add_.? (I (main!nl_basics.mul_.? (I d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                                            (I c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                                           )
                                                                                                                                                                                                                                                                                                                                                                                                                          ) (I (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I (main!nl_basics.mul_.? (I d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                                                (I b~4@)
                                                                                                                                                                                                                                                                                                                                                                                                                               )
                                                                                                                                                                                                                                                                                                                                                                                                                              ) (I (main!nl_basics.mul_.? (I c~6@) (I (main!nl_basics.mod_.? (I d~8@) (I m~10@)))))
                                                                                                                                                                                                                                                                                                                                                                                                                             )
                                                                                                                                                                                                                                                                                                                                                                                                                            ) (I m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                                         )))
                                                                                                                                                                                                                                                                                                                                                                                                                        ) (I m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                                     )))
                                                                                                                                                                                                                                                                                                                                                                                                                    ) (I m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                                  ))
                                                                                                                                                                                                                                                                                                                                                                                                                  (=>
                                                                                                                                                                                                                                                                                                                                                                                                                   (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                                                                                                                    %%location_label%%99
                                                                                                                                                                                                                                                                                                                                                                                                                    (main!nl_basics.eq_.? (I temp_99_0~7673@) (I temp_99_1~7733@))
 )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
 (get-info :version)
 (assert
  %%query%%
 )
 (set-option :rlimit 4294967295)
 (check-sat)
