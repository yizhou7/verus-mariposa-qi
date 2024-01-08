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

;; Function-Specs main::nl_basics::lemma_mul_properties_auto_1
(declare-fun ens%main!nl_basics.lemma_mul_properties_auto_1. (Int) Bool)
(assert
 (forall ((no%param@ Int)) (!
   (= (ens%main!nl_basics.lemma_mul_properties_auto_1. no%param@) (and
     (forall ((x~14$ Int) (y~16$ Int)) (!
       (= (Mul x~14$ y~16$) (Mul y~16$ x~14$))
       :pattern ((Mul x~14$ y~16$))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_0
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_0
     ))
     (forall ((x~45$ Int) (y~47$ Int) (z~49$ Int)) (!
       (= (Mul x~45$ (Mul y~47$ z~49$)) (Mul (Mul x~45$ y~47$) z~49$))
       :pattern ((Mul x~45$ (Mul y~47$ z~49$)))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_1
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_1
     ))
     (forall ((x~88$ Int) (y~90$ Int) (z~92$ Int)) (!
       (= (Mul x~88$ (Mul y~90$ z~92$)) (Mul (Mul x~88$ y~90$) z~92$))
       :pattern ((Mul (Mul x~88$ y~90$) z~92$))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_2
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_2
     ))
     (forall ((x~131$ Int) (y~133$ Int) (z~135$ Int)) (!
       (= (Mul x~131$ (Add y~133$ z~135$)) (Add (Mul x~131$ y~133$) (Mul x~131$ z~135$)))
       :pattern ((Mul x~131$ (Add y~133$ z~135$)))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_3
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_3
     ))
     (forall ((x~178$ Int) (y~180$ Int) (z~182$ Int)) (!
       (= (Mul (Add x~178$ y~180$) z~182$) (Add (Mul x~178$ z~182$) (Mul y~180$ z~182$)))
       :pattern ((Mul (Add x~178$ y~180$) z~182$))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_4
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_4
     ))
     (forall ((x~225$ Int) (y~227$ Int) (z~229$ Int)) (!
       (= (Mul x~225$ (Sub y~227$ z~229$)) (Sub (Mul x~225$ y~227$) (Mul x~225$ z~229$)))
       :pattern ((Mul x~225$ (Sub y~227$ z~229$)))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_5
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_5
     ))
     (forall ((x~272$ Int) (y~274$ Int) (z~276$ Int)) (!
       (= (Mul (Sub x~272$ y~274$) z~276$) (Sub (Mul x~272$ z~276$) (Mul y~274$ z~276$)))
       :pattern ((Mul (Sub x~272$ y~274$) z~276$))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_6
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_6
     ))
     (forall ((x~319$ Int) (y~321$ Int) (z~323$ Int)) (!
       (= (Mul x~319$ (Add y~321$ z~323$)) (Add (Mul x~319$ y~321$) (Mul x~319$ z~323$)))
       :pattern ((Add (Mul x~319$ y~321$) (Mul x~319$ z~323$)))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_7
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_7
     ))
     (forall ((x~366$ Int) (y~368$ Int) (z~370$ Int)) (!
       (= (Mul (Add x~366$ y~368$) z~370$) (Add (Mul x~366$ z~370$) (Mul y~368$ z~370$)))
       :pattern ((Add (Mul x~366$ z~370$) (Mul y~368$ z~370$)))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_8
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_8
     ))
     (forall ((x~413$ Int) (y~415$ Int) (z~417$ Int)) (!
       (= (Mul x~413$ (Sub y~415$ z~417$)) (Sub (Mul x~413$ y~415$) (Mul x~413$ z~417$)))
       :pattern ((Sub (Mul x~413$ y~415$) (Mul x~413$ z~417$)))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_9
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_9
     ))
     (forall ((x~460$ Int) (y~462$ Int) (z~464$ Int)) (!
       (= (Mul (Sub x~460$ y~462$) z~464$) (Sub (Mul x~460$ z~464$) (Mul y~462$ z~464$)))
       :pattern ((Sub (Mul x~460$ z~464$) (Mul y~462$ z~464$)))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_10
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_10
   ))))
   :pattern ((ens%main!nl_basics.lemma_mul_properties_auto_1. no%param@))
   :qid internal_ens__main!nl_basics.lemma_mul_properties_auto_1._definition
   :skolemid skolem_internal_ens__main!nl_basics.lemma_mul_properties_auto_1._definition
)))

;; Function-Def main::auto_0
;; mariposa_data/v_nl//2241149175590361516/nlqi_verus/src/main.rs:7:1: 36:40 (#0)
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
 (declare-const temp_0_0~305@ Int)
 (declare-const temp_0_1~402@ Int)
 (declare-const temp_1_0~487@ Int)
 (declare-const temp_1_1~548@ Int)
 (declare-const temp_2_0~645@ Int)
 (declare-const temp_2_1~718@ Int)
 (declare-const temp_3_0~807@ Int)
 (declare-const temp_3_1~872@ Int)
 (declare-const temp_4_0~957@ Int)
 (declare-const temp_4_1~1022@ Int)
 (declare-const temp_5_0~1099@ Int)
 (declare-const temp_5_1~1152@ Int)
 (declare-const temp_6_0~1233@ Int)
 (declare-const temp_6_1~1290@ Int)
 (declare-const temp_7_0~1371@ Int)
 (declare-const temp_7_1~1428@ Int)
 (declare-const temp_8_0~1513@ Int)
 (declare-const temp_8_1~1574@ Int)
 (declare-const temp_9_0~1659@ Int)
 (declare-const temp_9_1~1720@ Int)
 (declare-const temp_10_0~1813@ Int)
 (declare-const temp_10_1~1882@ Int)
 (declare-const temp_11_0~1971@ Int)
 (declare-const temp_11_1~2036@ Int)
 (declare-const temp_12_0~2113@ Int)
 (declare-const temp_12_1~2166@ Int)
 (declare-const temp_13_0~2255@ Int)
 (declare-const temp_13_1~2320@ Int)
 (declare-const temp_14_0~2377@ Int)
 (declare-const temp_14_1~2418@ Int)
 (declare-const temp_15_0~2511@ Int)
 (declare-const temp_15_1~2596@ Int)
 (declare-const temp_16_0~2669@ Int)
 (declare-const temp_16_1~2718@ Int)
 (declare-const temp_17_0~2807@ Int)
 (declare-const temp_17_1~2872@ Int)
 (declare-const temp_18_0~2937@ Int)
 (declare-const temp_18_1~2978@ Int)
 (declare-const temp_19_0~3063@ Int)
 (declare-const temp_19_1~3124@ Int)
 (declare-const temp_20_0~3209@ Int)
 (declare-const temp_20_1~3270@ Int)
 (declare-const temp_21_0~3355@ Int)
 (declare-const temp_21_1~3416@ Int)
 (declare-const temp_22_0~3493@ Int)
 (declare-const temp_22_1~3554@ Int)
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
 (declare-const %%query%% Bool)
 (assert
  (=>
   %%query%%
   (not (=>
     (= temp_0_0~305@ (Mul (Sub (Mul (Add a0~2@ b0~4@) (Mul b0~4@ c0~6@)) (Mul (Mul c0~6@ b0~4@)
         (Mul a0~2@ d0~8@)
        )
       ) (Mul (Mul (Mul d0~8@ d0~8@) (Mul b0~4@ c0~6@)) (Mul (Mul c0~6@ b0~4@) (Mul b0~4@ d0~8@)))
     ))
     (=>
      (= temp_0_1~402@ (Sub (Mul (Mul (Add a0~2@ b0~4@) (Mul b0~4@ c0~6@)) (Mul (Mul (Mul d0~8@
            d0~8@
           ) (Mul b0~4@ c0~6@)
          ) (Mul (Mul c0~6@ b0~4@) (Mul b0~4@ d0~8@))
         )
        ) (Mul (Mul (Mul c0~6@ b0~4@) (Mul a0~2@ d0~8@)) (Mul (Mul (Mul d0~8@ d0~8@) (Mul b0~4@
            c0~6@
           )
          ) (Mul (Mul c0~6@ b0~4@) (Mul b0~4@ d0~8@))
      ))))
      (and
       (=>
        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
        (=>
         %%location_label%%0
         (= temp_0_0~305@ temp_0_1~402@)
       ))
       (=>
        (= temp_0_0~305@ temp_0_1~402@)
        (=>
         (= temp_1_0~487@ (Mul (Mul (Mul a1~10@ (Mul c1~14@ c1~14@)) (Mul (Mul c1~14@ b1~12@)
             (Mul c1~14@ a1~10@)
            )
           ) (Add (Mul (Mul b1~12@ c1~14@) (Mul b1~12@ a1~10@)) (Mul (Mul c1~14@ c1~14@) (Add d1~16@
              a1~10@
         )))))
         (=>
          (= temp_1_1~548@ (Mul (Mul (Mul a1~10@ (Mul c1~14@ c1~14@)) (Mul (Mul c1~14@ b1~12@)
              (Mul c1~14@ a1~10@)
             )
            ) (Add (Mul (Mul b1~12@ c1~14@) (Mul b1~12@ a1~10@)) (Mul (Mul c1~14@ c1~14@) (Add d1~16@
               a1~10@
          )))))
          (and
           (=>
            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
            (=>
             %%location_label%%1
             (= temp_1_0~487@ temp_1_1~548@)
           ))
           (=>
            (= temp_1_0~487@ temp_1_1~548@)
            (=>
             (= temp_2_0~645@ (Mul (Mul (Sub (Mul c2~22@ b2~20@) (Mul c2~22@ a2~18@)) (Mul (Sub a2~18@
                  a2~18@
                 ) (Mul b2~20@ d2~24@)
                )
               ) (Mul (Add b2~20@ (Mul a2~18@ c2~22@)) (Mul (Mul c2~22@ c2~22@) (Mul c2~22@ 15)))
             ))
             (=>
              (= temp_2_1~718@ (Mul (Mul (Sub (Mul b2~20@ c2~22@) (Mul c2~22@ a2~18@)) (Mul (Sub a2~18@
                   a2~18@
                  ) (Mul b2~20@ d2~24@)
                 )
                ) (Mul (Add b2~20@ (Mul a2~18@ c2~22@)) (Mul (Mul c2~22@ c2~22@) (Mul c2~22@ 15)))
              ))
              (and
               (=>
                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                (=>
                 %%location_label%%2
                 (= temp_2_0~645@ temp_2_1~718@)
               ))
               (=>
                (= temp_2_0~645@ temp_2_1~718@)
                (=>
                 (= temp_3_0~807@ (Mul (Mul (Mul (Mul d3~32@ d3~32@) (Mul a3~26@ a3~26@)) (Mul (Mul a3~26@
                      c3~30@
                     ) (Add c3~30@ d3~32@)
                    )
                   ) (Add (Mul (Mul a3~26@ b3~28@) (Mul d3~32@ c3~30@)) (Mul (Mul d3~32@ d3~32@) (Mul a3~26@
                      c3~30@
                 )))))
                 (=>
                  (= temp_3_1~872@ (Mul (Mul (Mul (Mul d3~32@ d3~32@) (Mul a3~26@ a3~26@)) (Mul (Mul a3~26@
                       c3~30@
                      ) (Add c3~30@ d3~32@)
                     )
                    ) (Add (Mul (Mul a3~26@ b3~28@) (Mul d3~32@ c3~30@)) (Mul (Mul d3~32@ d3~32@) (Mul a3~26@
                       c3~30@
                  )))))
                  (and
                   (=>
                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                    (=>
                     %%location_label%%3
                     (= temp_3_0~807@ temp_3_1~872@)
                   ))
                   (=>
                    (= temp_3_0~807@ temp_3_1~872@)
                    (=>
                     (= temp_4_0~957@ (Mul (Mul (Mul (Mul d4~40@ a4~34@) (Mul a4~34@ a4~34@)) (Mul (Add c4~38@
                          c4~38@
                         ) (Add d4~40@ d4~40@)
                        )
                       ) (Mul (Mul d4~40@ (Sub b4~36@ c4~38@)) (Mul (Mul d4~40@ c4~38@) (Sub b4~36@ d4~40@)))
                     ))
                     (=>
                      (= temp_4_1~1022@ (Mul (Mul (Mul (Mul d4~40@ a4~34@) (Mul a4~34@ a4~34@)) (Mul (Add c4~38@
                           c4~38@
                          ) (Add d4~40@ d4~40@)
                         )
                        ) (Mul (Sub (Mul d4~40@ b4~36@) (Mul d4~40@ c4~38@)) (Mul (Mul d4~40@ c4~38@) (Sub b4~36@
                           d4~40@
                      )))))
                      (and
                       (=>
                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                        (=>
                         %%location_label%%4
                         (= temp_4_0~957@ temp_4_1~1022@)
                       ))
                       (=>
                        (= temp_4_0~957@ temp_4_1~1022@)
                        (=>
                         (= temp_5_0~1099@ (Mul (Mul (Mul (Mul c5~46@ c5~46@) (Add c5~46@ b5~44@)) c5~46@) (
                            Mul (Mul (Add a5~42@ b5~44@) (Mul a5~42@ c5~46@)) (Mul (Mul c5~46@ c5~46@) (Mul d5~48@
                              c5~46@
                         )))))
                         (=>
                          (= temp_5_1~1152@ (Mul (Mul (Mul (Add c5~46@ b5~44@) (Mul c5~46@ c5~46@)) c5~46@) (
                             Mul (Mul (Add a5~42@ b5~44@) (Mul a5~42@ c5~46@)) (Mul (Mul c5~46@ c5~46@) (Mul d5~48@
                               c5~46@
                          )))))
                          (and
                           (=>
                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                            (=>
                             %%location_label%%5
                             (= temp_5_0~1099@ temp_5_1~1152@)
                           ))
                           (=>
                            (= temp_5_0~1099@ temp_5_1~1152@)
                            (=>
                             (= temp_6_0~1233@ (Sub (Mul (Mul (Mul d6~56@ c6~54@) (Sub b6~52@ a6~50@)) (Mul (Mul d6~56@
                                  d6~56@
                                 ) c6~54@
                                )
                               ) (Add (Mul (Mul b6~52@ c6~54@) c6~54@) (Sub (Mul d6~56@ c6~54@) (Mul d6~56@ b6~52@)))
                             ))
                             (=>
                              (= temp_6_1~1290@ (Sub (Mul (Mul (Mul d6~56@ c6~54@) (Sub b6~52@ a6~50@)) (Mul d6~56@
                                  (Mul d6~56@ c6~54@)
                                 )
                                ) (Add (Mul (Mul b6~52@ c6~54@) c6~54@) (Sub (Mul d6~56@ c6~54@) (Mul d6~56@ b6~52@)))
                              ))
                              (and
                               (=>
                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                (=>
                                 %%location_label%%6
                                 (= temp_6_0~1233@ temp_6_1~1290@)
                               ))
                               (=>
                                (= temp_6_0~1233@ temp_6_1~1290@)
                                (=>
                                 (= temp_7_0~1371@ (Mul (Mul (Mul (Mul b7~60@ a7~58@) (Mul c7~62@ a7~58@)) (Mul (Mul d7~64@
                                      d7~64@
                                     ) b7~60@
                                    )
                                   ) (Sub (Add (Mul a7~58@ c7~62@) (Mul c7~62@ b7~60@)) (Mul (Mul b7~60@ d7~64@) b7~60@))
                                 ))
                                 (=>
                                  (= temp_7_1~1428@ (Mul (Mul (Mul b7~60@ a7~58@) (Mul c7~62@ a7~58@)) (Mul (Mul (Mul d7~64@
                                       d7~64@
                                      ) b7~60@
                                     ) (Sub (Add (Mul a7~58@ c7~62@) (Mul c7~62@ b7~60@)) (Mul (Mul b7~60@ d7~64@) b7~60@))
                                  )))
                                  (and
                                   (=>
                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                    (=>
                                     %%location_label%%7
                                     (= temp_7_0~1371@ temp_7_1~1428@)
                                   ))
                                   (=>
                                    (= temp_7_0~1371@ temp_7_1~1428@)
                                    (=>
                                     (= temp_8_0~1513@ (Mul (Mul (Mul (Add a8~66@ c8~70@) a8~66@) (Mul (Mul b8~68@ d8~72@)
                                         (Sub d8~72@ d8~72@)
                                        )
                                       ) (Mul (Mul (Mul d8~72@ c8~70@) (Mul c8~70@ b8~68@)) (Mul (Mul d8~72@ c8~70@) (Mul b8~68@
                                          a8~66@
                                     )))))
                                     (=>
                                      (= temp_8_1~1574@ (Mul (Mul (Mul (Mul d8~72@ c8~70@) (Mul c8~70@ b8~68@)) (Mul (Mul d8~72@
                                           c8~70@
                                          ) (Mul b8~68@ a8~66@)
                                         )
                                        ) (Mul (Mul (Add a8~66@ c8~70@) a8~66@) (Mul (Mul b8~68@ d8~72@) (Sub d8~72@ d8~72@)))
                                      ))
                                      (and
                                       (=>
                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                        (=>
                                         %%location_label%%8
                                         (= temp_8_0~1513@ temp_8_1~1574@)
                                       ))
                                       (=>
                                        (= temp_8_0~1513@ temp_8_1~1574@)
                                        (=>
                                         (= temp_9_0~1659@ (Mul (Mul (Mul (Mul d9~80@ b9~76@) (Mul c9~78@ d9~80@)) (Sub (Mul b9~76@
                                              b9~76@
                                             ) (Add c9~78@ a9~74@)
                                            )
                                           ) (Mul (Mul (Sub c9~78@ c9~78@) (Mul c9~78@ c9~78@)) (Mul (Mul b9~76@ b9~76@) d9~80@))
                                         ))
                                         (=>
                                          (= temp_9_1~1720@ (Mul (Mul (Mul (Mul (Mul d9~80@ b9~76@) (Mul c9~78@ d9~80@)) (Sub (Mul
                                                b9~76@ b9~76@
                                               ) (Add c9~78@ a9~74@)
                                              )
                                             ) (Mul (Sub c9~78@ c9~78@) (Mul c9~78@ c9~78@))
                                            ) (Mul (Mul b9~76@ b9~76@) d9~80@)
                                          ))
                                          (and
                                           (=>
                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                            (=>
                                             %%location_label%%9
                                             (= temp_9_0~1659@ temp_9_1~1720@)
                                           ))
                                           (=>
                                            (= temp_9_0~1659@ temp_9_1~1720@)
                                            (=>
                                             (= temp_10_0~1813@ (Sub (Mul (Mul (Add d10~88@ b10~84@) a10~82@) (Mul (Mul c10~86@ d10~88@)
                                                 d10~88@
                                                )
                                               ) (Mul (Mul (Mul d10~88@ c10~86@) (Mul d10~88@ a10~82@)) (Mul (Mul a10~82@ d10~88@)
                                                 (Add a10~82@ 14)
                                             ))))
                                             (=>
                                              (= temp_10_1~1882@ (Sub (Mul (Mul (Add d10~88@ b10~84@) a10~82@) (Mul (Mul c10~86@ d10~88@)
                                                  d10~88@
                                                 )
                                                ) (Mul (Mul (Mul a10~82@ d10~88@) (Add a10~82@ 14)) (Mul (Mul d10~88@ c10~86@) (Mul
                                                   d10~88@ a10~82@
                                              )))))
                                              (and
                                               (=>
                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                (=>
                                                 %%location_label%%10
                                                 (= temp_10_0~1813@ temp_10_1~1882@)
                                               ))
                                               (=>
                                                (= temp_10_0~1813@ temp_10_1~1882@)
                                                (=>
                                                 (= temp_11_0~1971@ (Add (Mul (Mul (Add a11~90@ d11~96@) (Mul b11~92@ d11~96@)) (Mul (
                                                      Mul c11~94@ a11~90@
                                                     ) (Sub c11~94@ a11~90@)
                                                    )
                                                   ) (Mul (Mul (Mul a11~90@ c11~94@) (Mul b11~92@ c11~94@)) (Sub (Mul b11~92@ c11~94@)
                                                     (Mul d11~96@ c11~94@)
                                                 ))))
                                                 (=>
                                                  (= temp_11_1~2036@ (Add (Mul (Mul (Add a11~90@ d11~96@) (Mul b11~92@ d11~96@)) (Mul (
                                                       Mul c11~94@ a11~90@
                                                      ) (Sub c11~94@ a11~90@)
                                                     )
                                                    ) (Mul (Mul (Mul a11~90@ c11~94@) (Mul c11~94@ b11~92@)) (Sub (Mul b11~92@ c11~94@)
                                                      (Mul d11~96@ c11~94@)
                                                  ))))
                                                  (and
                                                   (=>
                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                    (=>
                                                     %%location_label%%11
                                                     (= temp_11_0~1971@ temp_11_1~2036@)
                                                   ))
                                                   (=>
                                                    (= temp_11_0~1971@ temp_11_1~2036@)
                                                    (=>
                                                     (= temp_12_0~2113@ (Mul (Mul (Mul (Mul c12~102@ b12~100@) (Mul a12~98@ b12~100@)) c12~102@)
                                                       (Mul (Mul (Mul a12~98@ d12~104@) (Mul d12~104@ c12~102@)) (Mul (Mul d12~104@ c12~102@)
                                                         (Mul c12~102@ b12~100@)
                                                     ))))
                                                     (=>
                                                      (= temp_12_1~2166@ (Mul (Mul (Mul (Mul c12~102@ b12~100@) (Mul a12~98@ b12~100@)) c12~102@)
                                                        (Mul (Mul (Mul d12~104@ c12~102@) (Mul c12~102@ b12~100@)) (Mul (Mul a12~98@ d12~104@)
                                                          (Mul d12~104@ c12~102@)
                                                      ))))
                                                      (and
                                                       (=>
                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                        (=>
                                                         %%location_label%%12
                                                         (= temp_12_0~2113@ temp_12_1~2166@)
                                                       ))
                                                       (=>
                                                        (= temp_12_0~2113@ temp_12_1~2166@)
                                                        (=>
                                                         (= temp_13_0~2255@ (Sub (Mul (Add (Mul d13~112@ a13~106@) (Add b13~108@ d13~112@)) (
                                                             Mul (Sub b13~108@ b13~108@) (Add c13~110@ d13~112@)
                                                            )
                                                           ) (Mul (Mul (Mul b13~108@ c13~110@) (Mul a13~106@ b13~108@)) (Mul (Mul b13~108@ b13~108@)
                                                             (Mul c13~110@ a13~106@)
                                                         ))))
                                                         (=>
                                                          (= temp_13_1~2320@ (Sub (Mul (Mul (Sub b13~108@ b13~108@) (Add c13~110@ d13~112@)) (
                                                              Add (Mul d13~112@ a13~106@) (Add b13~108@ d13~112@)
                                                             )
                                                            ) (Mul (Mul (Mul b13~108@ c13~110@) (Mul a13~106@ b13~108@)) (Mul (Mul b13~108@ b13~108@)
                                                              (Mul c13~110@ a13~106@)
                                                          ))))
                                                          (and
                                                           (=>
                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                            (=>
                                                             %%location_label%%13
                                                             (= temp_13_0~2255@ temp_13_1~2320@)
                                                           ))
                                                           (=>
                                                            (= temp_13_0~2255@ temp_13_1~2320@)
                                                            (=>
                                                             (= temp_14_0~2377@ (Mul (Sub (Mul (Mul c14~118@ a14~114@) (Sub a14~114@ c14~118@)) (
                                                                 Sub (Sub b14~116@ b14~116@) b14~116@
                                                                )
                                                               ) b14~116@
                                                             ))
                                                             (=>
                                                              (= temp_14_1~2418@ (Mul (Sub (Sub (Mul (Mul c14~118@ a14~114@) a14~114@) (Mul (Mul c14~118@
                                                                    a14~114@
                                                                   ) c14~118@
                                                                  )
                                                                 ) (Sub (Sub b14~116@ b14~116@) b14~116@)
                                                                ) b14~116@
                                                              ))
                                                              (and
                                                               (=>
                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                (=>
                                                                 %%location_label%%14
                                                                 (= temp_14_0~2377@ temp_14_1~2418@)
                                                               ))
                                                               (=>
                                                                (= temp_14_0~2377@ temp_14_1~2418@)
                                                                (=>
                                                                 (= temp_15_0~2511@ (Mul (Mul (Mul (Mul a15~122@ b15~124@) (Mul c15~126@ b15~124@)) (
                                                                     Sub c15~126@ (Mul d15~128@ a15~122@)
                                                                    )
                                                                   ) (Mul (Sub (Mul d15~128@ d15~128@) (Mul c15~126@ c15~126@)) (Mul (Mul c15~126@ c15~126@)
                                                                     61
                                                                 ))))
                                                                 (=>
                                                                  (= temp_15_1~2596@ (Mul (Sub (Mul (Mul (Mul a15~122@ b15~124@) (Mul c15~126@ b15~124@))
                                                                      c15~126@
                                                                     ) (Mul (Mul (Mul a15~122@ b15~124@) (Mul c15~126@ b15~124@)) (Mul d15~128@ a15~122@))
                                                                    ) (Mul (Sub (Mul d15~128@ d15~128@) (Mul c15~126@ c15~126@)) (Mul (Mul c15~126@ c15~126@)
                                                                      61
                                                                  ))))
                                                                  (and
                                                                   (=>
                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                    (=>
                                                                     %%location_label%%15
                                                                     (= temp_15_0~2511@ temp_15_1~2596@)
                                                                   ))
                                                                   (=>
                                                                    (= temp_15_0~2511@ temp_15_1~2596@)
                                                                    (=>
                                                                     (= temp_16_0~2669@ (Mul a16~130@ (Mul (Add (Add b16~132@ d16~136@) (Mul 87 a16~130@))
                                                                        (Mul (Mul c16~134@ b16~132@) (Mul b16~132@ c16~134@))
                                                                     )))
                                                                     (=>
                                                                      (= temp_16_1~2718@ (Mul a16~130@ (Mul (Add (Add b16~132@ d16~136@) (Mul 87 a16~130@))
                                                                         (Mul (Mul c16~134@ b16~132@) (Mul c16~134@ b16~132@))
                                                                      )))
                                                                      (and
                                                                       (=>
                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                        (=>
                                                                         %%location_label%%16
                                                                         (= temp_16_0~2669@ temp_16_1~2718@)
                                                                       ))
                                                                       (=>
                                                                        (= temp_16_0~2669@ temp_16_1~2718@)
                                                                        (=>
                                                                         (= temp_17_0~2807@ (Mul (Mul (Add (Mul d17~144@ a17~138@) (Mul b17~140@ a17~138@)) (
                                                                             Mul (Add a17~138@ d17~144@) (Mul a17~138@ a17~138@)
                                                                            )
                                                                           ) (Mul (Mul (Mul c17~142@ d17~144@) (Mul b17~140@ b17~140@)) (Mul (Mul a17~138@ a17~138@)
                                                                             (Mul a17~138@ c17~142@)
                                                                         ))))
                                                                         (=>
                                                                          (= temp_17_1~2872@ (Mul (Mul (Add (Mul d17~144@ a17~138@) (Mul b17~140@ a17~138@)) (
                                                                              Mul (Mul a17~138@ a17~138@) (Add a17~138@ d17~144@)
                                                                             )
                                                                            ) (Mul (Mul (Mul c17~142@ d17~144@) (Mul b17~140@ b17~140@)) (Mul (Mul a17~138@ a17~138@)
                                                                              (Mul a17~138@ c17~142@)
                                                                          ))))
                                                                          (and
                                                                           (=>
                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                            (=>
                                                                             %%location_label%%17
                                                                             (= temp_17_0~2807@ temp_17_1~2872@)
                                                                           ))
                                                                           (=>
                                                                            (= temp_17_0~2807@ temp_17_1~2872@)
                                                                            (=>
                                                                             (= temp_18_0~2937@ (Mul (Mul (Mul (Mul d18~152@ a18~146@) (Mul c18~150@ d18~152@)) c18~150@)
                                                                               (Sub (Mul (Mul b18~148@ d18~152@) (Mul b18~148@ d18~152@)) a18~146@)
                                                                             ))
                                                                             (=>
                                                                              (= temp_18_1~2978@ (Mul (Mul c18~150@ (Mul (Mul d18~152@ a18~146@) (Mul c18~150@ d18~152@)))
                                                                                (Sub (Mul (Mul b18~148@ d18~152@) (Mul b18~148@ d18~152@)) a18~146@)
                                                                              ))
                                                                              (and
                                                                               (=>
                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                (=>
                                                                                 %%location_label%%18
                                                                                 (= temp_18_0~2937@ temp_18_1~2978@)
                                                                               ))
                                                                               (=>
                                                                                (= temp_18_0~2937@ temp_18_1~2978@)
                                                                                (=>
                                                                                 (= temp_19_0~3063@ (Mul (Mul (Mul (Mul a19~154@ d19~160@) (Sub c19~158@ b19~156@)) (
                                                                                     Mul (Mul d19~160@ b19~156@) d19~160@
                                                                                    )
                                                                                   ) (Mul (Mul (Mul a19~154@ a19~154@) (Mul a19~154@ b19~156@)) (Mul (Mul a19~154@ c19~158@)
                                                                                     (Mul c19~158@ b19~156@)
                                                                                 ))))
                                                                                 (=>
                                                                                  (= temp_19_1~3124@ (Mul (Mul (Mul (Mul a19~154@ d19~160@) (Sub c19~158@ b19~156@)) (
                                                                                      Mul (Mul d19~160@ b19~156@) d19~160@
                                                                                     )
                                                                                    ) (Mul (Mul (Mul a19~154@ a19~154@) (Mul b19~156@ a19~154@)) (Mul (Mul a19~154@ c19~158@)
                                                                                      (Mul c19~158@ b19~156@)
                                                                                  ))))
                                                                                  (and
                                                                                   (=>
                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                    (=>
                                                                                     %%location_label%%19
                                                                                     (= temp_19_0~3063@ temp_19_1~3124@)
                                                                                   ))
                                                                                   (=>
                                                                                    (= temp_19_0~3063@ temp_19_1~3124@)
                                                                                    (=>
                                                                                     (= temp_20_0~3209@ (Sub (Mul (Add a20~162@ (Mul d20~168@ c20~166@)) (Mul (Mul b20~164@
                                                                                          a20~162@
                                                                                         ) (Mul c20~166@ a20~162@)
                                                                                        )
                                                                                       ) (Mul (Mul (Mul d20~168@ d20~168@) (Mul c20~166@ c20~166@)) (Add (Mul a20~162@ b20~164@)
                                                                                         (Mul c20~166@ b20~164@)
                                                                                     ))))
                                                                                     (=>
                                                                                      (= temp_20_1~3270@ (Sub (Mul (Add a20~162@ (Mul d20~168@ c20~166@)) (Mul (Mul b20~164@
                                                                                           a20~162@
                                                                                          ) (Mul c20~166@ a20~162@)
                                                                                         )
                                                                                        ) (Mul (Mul (Mul c20~166@ c20~166@) (Mul d20~168@ d20~168@)) (Add (Mul a20~162@ b20~164@)
                                                                                          (Mul c20~166@ b20~164@)
                                                                                      ))))
                                                                                      (and
                                                                                       (=>
                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                        (=>
                                                                                         %%location_label%%20
                                                                                         (= temp_20_0~3209@ temp_20_1~3270@)
                                                                                       ))
                                                                                       (=>
                                                                                        (= temp_20_0~3209@ temp_20_1~3270@)
                                                                                        (=>
                                                                                         (= temp_21_0~3355@ (Mul (Mul (Mul (Mul d21~176@ c21~174@) (Mul b21~172@ b21~172@)) (
                                                                                             Mul (Mul c21~174@ b21~172@) (Mul c21~174@ a21~170@)
                                                                                            )
                                                                                           ) (Add (Sub (Mul d21~176@ d21~176@) (Mul a21~170@ b21~172@)) (Mul (Mul d21~176@ c21~174@)
                                                                                             a21~170@
                                                                                         ))))
                                                                                         (=>
                                                                                          (= temp_21_1~3416@ (Mul (Mul (Mul (Mul d21~176@ c21~174@) (Mul b21~172@ b21~172@)) (
                                                                                              Mul (Mul c21~174@ b21~172@) (Mul a21~170@ c21~174@)
                                                                                             )
                                                                                            ) (Add (Sub (Mul d21~176@ d21~176@) (Mul a21~170@ b21~172@)) (Mul (Mul d21~176@ c21~174@)
                                                                                              a21~170@
                                                                                          ))))
                                                                                          (and
                                                                                           (=>
                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                            (=>
                                                                                             %%location_label%%21
                                                                                             (= temp_21_0~3355@ temp_21_1~3416@)
                                                                                           ))
                                                                                           (=>
                                                                                            (= temp_21_0~3355@ temp_21_1~3416@)
                                                                                            (=>
                                                                                             (= temp_22_0~3493@ (Mul (Mul b22~180@ (Sub (Sub b22~180@ d22~184@) (Mul c22~182@ d22~184@)))
                                                                                               (Mul (Mul (Mul b22~180@ d22~184@) (Mul c22~182@ c22~182@)) (Mul (Add b22~180@ c22~182@)
                                                                                                 (Mul c22~182@ d22~184@)
                                                                                             ))))
                                                                                             (=>
                                                                                              (= temp_22_1~3554@ (Mul (Mul b22~180@ (Sub (Sub b22~180@ d22~184@) (Mul c22~182@ d22~184@)))
                                                                                                (Mul (Mul (Mul b22~180@ d22~184@) (Mul c22~182@ c22~182@)) (Add (Mul b22~180@ (Mul c22~182@
                                                                                                    d22~184@
                                                                                                   )
                                                                                                  ) (Mul c22~182@ (Mul c22~182@ d22~184@))
                                                                                              ))))
                                                                                              (=>
                                                                                               (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                               (=>
                                                                                                %%location_label%%22
                                                                                                (= temp_22_0~3493@ temp_22_1~3554@)
 )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
 (get-info :version)
 (assert
  %%query%%
 )
 (set-option :rlimit 4294967295)
 (check-sat)
 (set-option :rlimit 0)
(pop)
