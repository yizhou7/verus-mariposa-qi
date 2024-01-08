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
;; mariposa_data/v_nl//6878346404358128900/nlqi_verus/src/main.rs:7:1: 36:40 (#0)
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
 (declare-const temp_0_0~293@ Int)
 (declare-const temp_0_1~342@ Int)
 (declare-const temp_1_0~427@ Int)
 (declare-const temp_1_1~488@ Int)
 (declare-const temp_2_0~597@ Int)
 (declare-const temp_2_1~714@ Int)
 (declare-const temp_3_0~803@ Int)
 (declare-const temp_3_1~864@ Int)
 (declare-const temp_4_0~953@ Int)
 (declare-const temp_4_1~1018@ Int)
 (declare-const temp_5_0~1079@ Int)
 (declare-const temp_5_1~1136@ Int)
 (declare-const temp_6_0~1233@ Int)
 (declare-const temp_6_1~1334@ Int)
 (declare-const temp_7_0~1423@ Int)
 (declare-const temp_7_1~1496@ Int)
 (declare-const temp_8_0~1581@ Int)
 (declare-const temp_8_1~1642@ Int)
 (declare-const temp_9_0~1731@ Int)
 (declare-const temp_9_1~1796@ Int)
 (declare-const temp_10_0~1885@ Int)
 (declare-const temp_10_1~1950@ Int)
 (declare-const temp_11_0~2039@ Int)
 (declare-const temp_11_1~2112@ Int)
 (declare-const temp_12_0~2185@ Int)
 (declare-const temp_12_1~2234@ Int)
 (declare-const temp_13_0~2319@ Int)
 (declare-const temp_13_1~2380@ Int)
 (declare-const temp_14_0~2469@ Int)
 (declare-const temp_14_1~2542@ Int)
 (declare-const temp_15_0~2615@ Int)
 (declare-const temp_15_1~2664@ Int)
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
 (declare-const %%query%% Bool)
 (assert
  (=>
   %%query%%
   (not (=>
     (= temp_0_0~293@ (Sub (Add (Add (Mul b0~4@ c0~6@) (Mul c0~6@ d0~8@)) a0~2@) (Add (Mul
         (Sub d0~8@ b0~4@) (Mul b0~4@ b0~4@)
        ) (Sub (Mul d0~8@ c0~6@) (Mul b0~4@ c0~6@))
     )))
     (=>
      (= temp_0_1~342@ (Sub (Add (Add (Mul b0~4@ c0~6@) (Mul c0~6@ d0~8@)) a0~2@) (Add (Mul
          (Sub d0~8@ b0~4@) (Mul b0~4@ b0~4@)
         ) (Mul (Sub d0~8@ b0~4@) c0~6@)
      )))
      (and
       (=>
        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
        (=>
         %%location_label%%0
         (= temp_0_0~293@ temp_0_1~342@)
       ))
       (=>
        (= temp_0_0~293@ temp_0_1~342@)
        (=>
         (= temp_1_0~427@ (Mul (Mul (Mul (Mul d1~16@ d1~16@) (Mul a1~10@ a1~10@)) (Mul (Add a1~10@
              c1~14@
             ) (Mul a1~10@ c1~14@)
            )
           ) (Mul (Add a1~10@ (Mul d1~16@ c1~14@)) (Mul (Mul d1~16@ d1~16@) (Add d1~16@ b1~12@)))
         ))
         (=>
          (= temp_1_1~488@ (Mul (Mul (Mul (Mul d1~16@ d1~16@) (Mul a1~10@ a1~10@)) (Mul (Add a1~10@
               c1~14@
              ) (Mul a1~10@ c1~14@)
             )
            ) (Mul (Add a1~10@ (Mul c1~14@ d1~16@)) (Mul (Mul d1~16@ d1~16@) (Add d1~16@ b1~12@)))
          ))
          (and
           (=>
            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
            (=>
             %%location_label%%1
             (= temp_1_0~427@ temp_1_1~488@)
           ))
           (=>
            (= temp_1_0~427@ temp_1_1~488@)
            (=>
             (= temp_2_0~597@ (Mul (Mul (Mul (Mul d2~24@ c2~22@) (Mul c2~22@ c2~22@)) (Mul (Mul c2~22@
                  a2~18@
                 ) (Mul b2~20@ b2~20@)
                )
               ) (Add (Mul (Mul c2~22@ b2~20@) (Mul 76 a2~18@)) (Mul (Add 94 a2~18@) a2~18@))
             ))
             (=>
              (= temp_2_1~714@ (Add (Mul (Mul (Mul (Mul d2~24@ c2~22@) (Mul c2~22@ c2~22@)) (Mul (Mul
                    c2~22@ a2~18@
                   ) (Mul b2~20@ b2~20@)
                  )
                 ) (Mul (Mul c2~22@ b2~20@) (Mul 76 a2~18@))
                ) (Mul (Mul (Mul (Mul d2~24@ c2~22@) (Mul c2~22@ c2~22@)) (Mul (Mul c2~22@ a2~18@) (
                    Mul b2~20@ b2~20@
                  ))
                 ) (Mul (Add 94 a2~18@) a2~18@)
              )))
              (and
               (=>
                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                (=>
                 %%location_label%%2
                 (= temp_2_0~597@ temp_2_1~714@)
               ))
               (=>
                (= temp_2_0~597@ temp_2_1~714@)
                (=>
                 (= temp_3_0~803@ (Mul (Mul (Mul (Mul a3~26@ c3~30@) (Mul d3~32@ c3~30@)) (Mul (Mul a3~26@
                      b3~28@
                     ) (Mul a3~26@ a3~26@)
                    )
                   ) (Mul (Add (Mul d3~32@ c3~30@) (Mul d3~32@ d3~32@)) (Sub (Mul b3~28@ b3~28@) (Mul a3~26@
                      a3~26@
                 )))))
                 (=>
                  (= temp_3_1~864@ (Mul (Mul (Mul (Mul a3~26@ c3~30@) (Mul d3~32@ c3~30@)) (Mul (Mul a3~26@
                       b3~28@
                      ) (Mul a3~26@ a3~26@)
                     )
                    ) (Mul (Mul d3~32@ (Add c3~30@ d3~32@)) (Sub (Mul b3~28@ b3~28@) (Mul a3~26@ a3~26@)))
                  ))
                  (and
                   (=>
                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                    (=>
                     %%location_label%%3
                     (= temp_3_0~803@ temp_3_1~864@)
                   ))
                   (=>
                    (= temp_3_0~803@ temp_3_1~864@)
                    (=>
                     (= temp_4_0~953@ (Mul (Mul (Mul (Add a4~34@ a4~34@) (Mul c4~38@ d4~40@)) (Mul (Mul c4~38@
                          b4~36@
                         ) (Mul b4~36@ a4~34@)
                        )
                       ) (Mul (Mul (Mul b4~36@ a4~34@) (Mul c4~38@ a4~34@)) (Add (Mul c4~38@ a4~34@) (Mul b4~36@
                          b4~36@
                     )))))
                     (=>
                      (= temp_4_1~1018@ (Mul (Mul (Mul (Mul (Add a4~34@ a4~34@) c4~38@) d4~40@) (Mul (Mul c4~38@
                           b4~36@
                          ) (Mul b4~36@ a4~34@)
                         )
                        ) (Mul (Mul (Mul b4~36@ a4~34@) (Mul c4~38@ a4~34@)) (Add (Mul c4~38@ a4~34@) (Mul b4~36@
                           b4~36@
                      )))))
                      (and
                       (=>
                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                        (=>
                         %%location_label%%4
                         (= temp_4_0~953@ temp_4_1~1018@)
                       ))
                       (=>
                        (= temp_4_0~953@ temp_4_1~1018@)
                        (=>
                         (= temp_5_0~1079@ (Mul (Mul a5~42@ (Mul (Mul c5~46@ c5~46@) (Sub a5~42@ d5~48@))) (
                            Sub (Mul (Mul c5~46@ a5~42@) b5~44@) c5~46@
                         )))
                         (=>
                          (= temp_5_1~1136@ (Sub (Mul (Mul a5~42@ (Mul (Mul c5~46@ c5~46@) (Sub a5~42@ d5~48@)))
                             (Mul (Mul c5~46@ a5~42@) b5~44@)
                            ) (Mul (Mul a5~42@ (Mul (Mul c5~46@ c5~46@) (Sub a5~42@ d5~48@))) c5~46@)
                          ))
                          (and
                           (=>
                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                            (=>
                             %%location_label%%5
                             (= temp_5_0~1079@ temp_5_1~1136@)
                           ))
                           (=>
                            (= temp_5_0~1079@ temp_5_1~1136@)
                            (=>
                             (= temp_6_0~1233@ (Mul (Add (Mul (Mul c6~54@ c6~54@) (Mul c6~54@ 3)) (Mul (Mul c6~54@
                                  a6~50@
                                 ) (Mul c6~54@ a6~50@)
                                )
                               ) (Mul (Mul (Sub b6~52@ d6~56@) a6~50@) (Mul (Mul a6~50@ c6~54@) (Mul d6~56@ d6~56@)))
                             ))
                             (=>
                              (= temp_6_1~1334@ (Add (Mul (Mul (Mul c6~54@ c6~54@) (Mul c6~54@ 3)) (Mul (Mul (Sub b6~52@
                                    d6~56@
                                   ) a6~50@
                                  ) (Mul (Mul a6~50@ c6~54@) (Mul d6~56@ d6~56@))
                                 )
                                ) (Mul (Mul (Mul c6~54@ a6~50@) (Mul c6~54@ a6~50@)) (Mul (Mul (Sub b6~52@ d6~56@) a6~50@)
                                  (Mul (Mul a6~50@ c6~54@) (Mul d6~56@ d6~56@))
                              ))))
                              (and
                               (=>
                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                (=>
                                 %%location_label%%6
                                 (= temp_6_0~1233@ temp_6_1~1334@)
                               ))
                               (=>
                                (= temp_6_0~1233@ temp_6_1~1334@)
                                (=>
                                 (= temp_7_0~1423@ (Add (Mul (Mul (Mul b7~60@ d7~64@) (Mul a7~58@ b7~60@)) (Mul (Mul d7~64@
                                      b7~60@
                                     ) (Sub d7~64@ b7~60@)
                                    )
                                   ) (Mul (Add (Mul a7~58@ c7~62@) (Sub b7~60@ d7~64@)) (Mul (Mul d7~64@ b7~60@) (Mul c7~62@
                                      a7~58@
                                 )))))
                                 (=>
                                  (= temp_7_1~1496@ (Add (Mul (Mul (Mul b7~60@ d7~64@) (Mul a7~58@ b7~60@)) (Sub (Mul (Mul
                                        d7~64@ b7~60@
                                       ) d7~64@
                                      ) (Mul (Mul d7~64@ b7~60@) b7~60@)
                                     )
                                    ) (Mul (Add (Mul a7~58@ c7~62@) (Sub b7~60@ d7~64@)) (Mul (Mul d7~64@ b7~60@) (Mul c7~62@
                                       a7~58@
                                  )))))
                                  (and
                                   (=>
                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                    (=>
                                     %%location_label%%7
                                     (= temp_7_0~1423@ temp_7_1~1496@)
                                   ))
                                   (=>
                                    (= temp_7_0~1423@ temp_7_1~1496@)
                                    (=>
                                     (= temp_8_0~1581@ (Mul (Mul (Mul (Mul c8~70@ d8~72@) (Sub a8~66@ b8~68@)) (Mul c8~70@
                                         (Mul c8~70@ a8~66@)
                                        )
                                       ) (Mul (Mul (Mul a8~66@ a8~66@) (Sub c8~70@ b8~68@)) (Mul (Mul d8~72@ d8~72@) (Mul c8~70@
                                          d8~72@
                                     )))))
                                     (=>
                                      (= temp_8_1~1642@ (Mul (Mul (Mul (Mul a8~66@ a8~66@) (Sub c8~70@ b8~68@)) (Mul (Mul d8~72@
                                           d8~72@
                                          ) (Mul c8~70@ d8~72@)
                                         )
                                        ) (Mul (Mul (Mul c8~70@ d8~72@) (Sub a8~66@ b8~68@)) (Mul c8~70@ (Mul c8~70@ a8~66@)))
                                      ))
                                      (and
                                       (=>
                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                        (=>
                                         %%location_label%%8
                                         (= temp_8_0~1581@ temp_8_1~1642@)
                                       ))
                                       (=>
                                        (= temp_8_0~1581@ temp_8_1~1642@)
                                        (=>
                                         (= temp_9_0~1731@ (Mul (Mul (Mul (Mul a9~74@ b9~76@) (Mul c9~78@ c9~78@)) (Mul (Sub c9~78@
                                              a9~74@
                                             ) (Sub b9~76@ a9~74@)
                                            )
                                           ) (Add (Mul (Mul b9~76@ c9~78@) (Mul b9~76@ b9~76@)) (Sub (Mul a9~74@ b9~76@) (Mul b9~76@
                                              c9~78@
                                         )))))
                                         (=>
                                          (= temp_9_1~1796@ (Mul (Mul (Mul a9~74@ b9~76@) (Mul (Mul c9~78@ c9~78@) (Mul (Sub c9~78@
                                                a9~74@
                                               ) (Sub b9~76@ a9~74@)
                                             ))
                                            ) (Add (Mul (Mul b9~76@ c9~78@) (Mul b9~76@ b9~76@)) (Sub (Mul a9~74@ b9~76@) (Mul b9~76@
                                               c9~78@
                                          )))))
                                          (and
                                           (=>
                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                            (=>
                                             %%location_label%%9
                                             (= temp_9_0~1731@ temp_9_1~1796@)
                                           ))
                                           (=>
                                            (= temp_9_0~1731@ temp_9_1~1796@)
                                            (=>
                                             (= temp_10_0~1885@ (Mul (Mul (Add (Mul b10~84@ c10~86@) (Add d10~88@ b10~84@)) (Mul (
                                                  Mul d10~88@ a10~82@
                                                 ) (Mul a10~82@ a10~82@)
                                                )
                                               ) (Add (Mul (Mul c10~86@ a10~82@) (Mul c10~86@ b10~84@)) (Sub (Mul d10~88@ a10~82@)
                                                 (Mul c10~86@ b10~84@)
                                             ))))
                                             (=>
                                              (= temp_10_1~1950@ (Mul (Mul (Add (Mul b10~84@ c10~86@) (Add d10~88@ b10~84@)) (Mul (
                                                   Mul d10~88@ a10~82@
                                                  ) (Mul a10~82@ a10~82@)
                                                 )
                                                ) (Add (Mul (Mul c10~86@ a10~82@) (Mul c10~86@ b10~84@)) (Sub (Mul a10~82@ d10~88@)
                                                  (Mul c10~86@ b10~84@)
                                              ))))
                                              (and
                                               (=>
                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                (=>
                                                 %%location_label%%10
                                                 (= temp_10_0~1885@ temp_10_1~1950@)
                                               ))
                                               (=>
                                                (= temp_10_0~1885@ temp_10_1~1950@)
                                                (=>
                                                 (= temp_11_0~2039@ (Mul (Add (Mul (Sub b11~92@ d11~96@) (Mul c11~94@ d11~96@)) (Mul (
                                                      Mul d11~96@ b11~92@
                                                     ) (Mul a11~90@ d11~96@)
                                                    )
                                                   ) (Mul (Mul (Mul c11~94@ a11~90@) (Mul c11~94@ a11~90@)) (Mul (Add c11~94@ c11~94@)
                                                     (Sub b11~92@ a11~90@)
                                                 ))))
                                                 (=>
                                                  (= temp_11_1~2112@ (Mul (Add (Sub (Mul b11~92@ (Mul c11~94@ d11~96@)) (Mul d11~96@ (Mul
                                                        c11~94@ d11~96@
                                                      ))
                                                     ) (Mul (Mul d11~96@ b11~92@) (Mul a11~90@ d11~96@))
                                                    ) (Mul (Mul (Mul c11~94@ a11~90@) (Mul c11~94@ a11~90@)) (Mul (Add c11~94@ c11~94@)
                                                      (Sub b11~92@ a11~90@)
                                                  ))))
                                                  (and
                                                   (=>
                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                    (=>
                                                     %%location_label%%11
                                                     (= temp_11_0~2039@ temp_11_1~2112@)
                                                   ))
                                                   (=>
                                                    (= temp_11_0~2039@ temp_11_1~2112@)
                                                    (=>
                                                     (= temp_12_0~2185@ (Mul (Mul (Mul (Mul b12~100@ a12~98@) (Mul c12~102@ d12~104@)) (Mul
                                                         (Add d12~104@ d12~104@) (Mul a12~98@ c12~102@)
                                                        )
                                                       ) (Mul a12~98@ (Add d12~104@ (Mul a12~98@ c12~102@)))
                                                     ))
                                                     (=>
                                                      (= temp_12_1~2234@ (Mul (Mul (Mul (Mul b12~100@ a12~98@) (Mul c12~102@ d12~104@)) (Mul
                                                          (Add d12~104@ d12~104@) (Mul c12~102@ a12~98@)
                                                         )
                                                        ) (Mul a12~98@ (Add d12~104@ (Mul a12~98@ c12~102@)))
                                                      ))
                                                      (and
                                                       (=>
                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                        (=>
                                                         %%location_label%%12
                                                         (= temp_12_0~2185@ temp_12_1~2234@)
                                                       ))
                                                       (=>
                                                        (= temp_12_0~2185@ temp_12_1~2234@)
                                                        (=>
                                                         (= temp_13_0~2319@ (Mul (Mul (Mul b13~108@ (Mul d13~112@ c13~110@)) (Mul (Mul b13~108@
                                                              d13~112@
                                                             ) (Mul b13~108@ d13~112@)
                                                            )
                                                           ) (Mul (Add (Mul c13~110@ d13~112@) (Mul d13~112@ d13~112@)) (Mul (Add a13~106@ b13~108@)
                                                             (Mul a13~106@ c13~110@)
                                                         ))))
                                                         (=>
                                                          (= temp_13_1~2380@ (Mul (Mul (Mul b13~108@ (Mul d13~112@ c13~110@)) (Mul (Mul b13~108@
                                                               d13~112@
                                                              ) (Mul b13~108@ d13~112@)
                                                             )
                                                            ) (Mul (Add (Mul c13~110@ d13~112@) (Mul d13~112@ d13~112@)) (Mul (Add a13~106@ b13~108@)
                                                              (Mul c13~110@ a13~106@)
                                                          ))))
                                                          (and
                                                           (=>
                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                            (=>
                                                             %%location_label%%13
                                                             (= temp_13_0~2319@ temp_13_1~2380@)
                                                           ))
                                                           (=>
                                                            (= temp_13_0~2319@ temp_13_1~2380@)
                                                            (=>
                                                             (= temp_14_0~2469@ (Mul (Sub (Sub (Sub d14~120@ c14~118@) (Mul b14~116@ a14~114@)) (
                                                                 Mul (Mul a14~114@ a14~114@) (Mul d14~120@ a14~114@)
                                                                )
                                                               ) (Mul (Mul (Mul c14~118@ b14~116@) (Sub c14~118@ b14~116@)) (Mul (Add d14~120@ a14~114@)
                                                                 (Sub a14~114@ b14~116@)
                                                             ))))
                                                             (=>
                                                              (= temp_14_1~2542@ (Mul (Sub (Sub (Sub d14~120@ c14~118@) (Mul b14~116@ a14~114@)) (
                                                                  Mul (Mul a14~114@ a14~114@) (Mul d14~120@ a14~114@)
                                                                 )
                                                                ) (Mul (Sub (Mul (Mul c14~118@ b14~116@) c14~118@) (Mul (Mul c14~118@ b14~116@) b14~116@))
                                                                 (Mul (Add d14~120@ a14~114@) (Sub a14~114@ b14~116@))
                                                              )))
                                                              (and
                                                               (=>
                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                (=>
                                                                 %%location_label%%14
                                                                 (= temp_14_0~2469@ temp_14_1~2542@)
                                                               ))
                                                               (=>
                                                                (= temp_14_0~2469@ temp_14_1~2542@)
                                                                (=>
                                                                 (= temp_15_0~2615@ (Sub d15~128@ (Add (Mul (Mul a15~122@ a15~122@) (Mul c15~126@ d15~128@))
                                                                    (Mul (Mul d15~128@ b15~124@) (Mul 53 a15~122@))
                                                                 )))
                                                                 (=>
                                                                  (= temp_15_1~2664@ (Sub d15~128@ (Add (Mul (Mul a15~122@ a15~122@) (Mul c15~126@ d15~128@))
                                                                     (Mul (Mul d15~128@ b15~124@) (Mul a15~122@ 53))
                                                                  )))
                                                                  (=>
                                                                   (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                   (=>
                                                                    %%location_label%%15
                                                                    (= temp_15_0~2615@ temp_15_1~2664@)
 )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
 (get-info :version)
 (assert
  %%query%%
 )
 (set-option :rlimit 4294967295)
 (check-sat)
 (set-option :rlimit 0)
(pop)
