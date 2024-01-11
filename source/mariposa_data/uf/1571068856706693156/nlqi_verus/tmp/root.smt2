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
(declare-sort main!nl_basics.Elem. 0)
(declare-datatypes ((tuple%0. 0)) (((tuple%0./tuple%0))))
(declare-const TYPE%main!nl_basics.Elem. Type)
(declare-const TYPE%tuple%0. Type)
(declare-fun Poly%main!nl_basics.Elem. (main!nl_basics.Elem.) Poly)
(declare-fun %Poly%main!nl_basics.Elem. (Poly) main!nl_basics.Elem.)
(declare-fun Poly%tuple%0. (tuple%0.) Poly)
(declare-fun %Poly%tuple%0. (Poly) tuple%0.)
(assert
 (forall ((x@ main!nl_basics.Elem.)) (!
   (= x@ (%Poly%main!nl_basics.Elem. (Poly%main!nl_basics.Elem. x@)))
   :pattern ((Poly%main!nl_basics.Elem. x@))
   :qid internal_main__nl_basics__Elem_box_axiom_definition
   :skolemid skolem_internal_main__nl_basics__Elem_box_axiom_definition
)))
(assert
 (forall ((x@ Poly)) (!
   (=>
    (has_type x@ TYPE%main!nl_basics.Elem.)
    (= x@ (Poly%main!nl_basics.Elem. (%Poly%main!nl_basics.Elem. x@)))
   )
   :pattern ((has_type x@ TYPE%main!nl_basics.Elem.))
   :qid internal_main__nl_basics__Elem_unbox_axiom_definition
   :skolemid skolem_internal_main__nl_basics__Elem_unbox_axiom_definition
)))
(assert
 (forall ((x@ main!nl_basics.Elem.)) (!
   (has_type (Poly%main!nl_basics.Elem. x@) TYPE%main!nl_basics.Elem.)
   :pattern ((has_type (Poly%main!nl_basics.Elem. x@) TYPE%main!nl_basics.Elem.))
   :qid internal_main__nl_basics__Elem_has_type_always_definition
   :skolemid skolem_internal_main__nl_basics__Elem_has_type_always_definition
)))
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

;; Function-Decl main::nl_basics::as_elem
(declare-fun main!nl_basics.as_elem.? (Poly) main!nl_basics.Elem.)

;; Function-Decl main::nl_basics::eq_
(declare-fun main!nl_basics.eq_.? (Poly Poly) Bool)

;; Function-Decl main::nl_basics::add_
(declare-fun main!nl_basics.add_.? (Poly Poly) main!nl_basics.Elem.)

;; Function-Decl main::nl_basics::sub_
(declare-fun main!nl_basics.sub_.? (Poly Poly) main!nl_basics.Elem.)

;; Function-Decl main::nl_basics::mul_
(declare-fun main!nl_basics.mul_.? (Poly Poly) main!nl_basics.Elem.)

;; Function-Decl main::nl_basics::mod_
(declare-fun main!nl_basics.mod_.? (Poly Poly) main!nl_basics.Elem.)

;; Function-Specs main::nl_basics::lemma_mul_properties_auto_1
(declare-fun ens%main!nl_basics.lemma_mul_properties_auto_1. (Int) Bool)
(assert
 (forall ((no%param@ Int)) (!
   (= (ens%main!nl_basics.lemma_mul_properties_auto_1. no%param@) (and
     (forall ((x~14$ Poly) (y~16$ Poly)) (!
       (=>
        (and
         (has_type x~14$ TYPE%main!nl_basics.Elem.)
         (has_type y~16$ TYPE%main!nl_basics.Elem.)
        )
        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? x~14$ y~16$))
         (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? y~16$ x~14$))
       ))
       :pattern ((main!nl_basics.add_.? x~14$ y~16$))
       :pattern ((main!nl_basics.add_.? y~16$ x~14$))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_0
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_0
     ))
     (forall ((x~45$ Poly) (y~47$ Poly)) (!
       (=>
        (and
         (has_type x~45$ TYPE%main!nl_basics.Elem.)
         (has_type y~47$ TYPE%main!nl_basics.Elem.)
        )
        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? x~45$ y~47$))
         (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? y~47$ x~45$))
       ))
       :pattern ((main!nl_basics.mul_.? x~45$ y~47$))
       :pattern ((main!nl_basics.mul_.? y~47$ x~45$))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_1
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_1
     ))
     (forall ((x~76$ Poly) (y~78$ Poly) (z~80$ Poly)) (!
       (=>
        (and
         (has_type x~76$ TYPE%main!nl_basics.Elem.)
         (has_type y~78$ TYPE%main!nl_basics.Elem.)
         (has_type z~80$ TYPE%main!nl_basics.Elem.)
        )
        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? x~76$ (Poly%main!nl_basics.Elem.
            (main!nl_basics.mul_.? y~78$ z~80$)
          ))
         ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
             x~76$ y~78$
            )
           ) z~80$
       ))))
       :pattern ((main!nl_basics.mul_.? x~76$ (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
           y~78$ z~80$
       ))))
       :pattern ((main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? x~76$
           y~78$
          )
         ) z~80$
       ))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_2
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_2
     ))
     (forall ((x~121$ Poly) (y~123$ Poly) (z~125$ Poly)) (!
       (=>
        (and
         (has_type x~121$ TYPE%main!nl_basics.Elem.)
         (has_type y~123$ TYPE%main!nl_basics.Elem.)
         (has_type z~125$ TYPE%main!nl_basics.Elem.)
        )
        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? x~121$ (Poly%main!nl_basics.Elem.
            (main!nl_basics.add_.? y~123$ z~125$)
          ))
         ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
             x~121$ y~123$
            )
           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? x~121$ z~125$))
       ))))
       :pattern ((main!nl_basics.mul_.? x~121$ (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
           y~123$ z~125$
       ))))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_3
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_3
     ))
     (forall ((x~171$ Poly) (y~173$ Poly) (z~175$ Poly)) (!
       (=>
        (and
         (has_type x~171$ TYPE%main!nl_basics.Elem.)
         (has_type y~173$ TYPE%main!nl_basics.Elem.)
         (has_type z~175$ TYPE%main!nl_basics.Elem.)
        )
        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem.
            (main!nl_basics.add_.? x~171$ y~173$)
           ) z~175$
          )
         ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
             x~171$ z~175$
            )
           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? y~173$ z~175$))
       ))))
       :pattern ((main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? x~171$
           y~173$
          )
         ) z~175$
       ))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_4
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_4
     ))
     (forall ((x~221$ Poly) (y~223$ Poly) (z~225$ Poly)) (!
       (=>
        (and
         (has_type x~221$ TYPE%main!nl_basics.Elem.)
         (has_type y~223$ TYPE%main!nl_basics.Elem.)
         (has_type z~225$ TYPE%main!nl_basics.Elem.)
        )
        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem.
            (main!nl_basics.sub_.? y~223$ z~225$)
           ) x~221$
          )
         ) (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
             y~223$ x~221$
            )
           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? z~225$ x~221$))
       ))))
       :pattern ((main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? y~223$
           z~225$
          )
         ) x~221$
       ))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_5
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_5
     ))
     (forall ((x~271$ Poly) (y~273$ Poly) (z~275$ Poly)) (!
       (=>
        (and
         (has_type x~271$ TYPE%main!nl_basics.Elem.)
         (has_type y~273$ TYPE%main!nl_basics.Elem.)
         (has_type z~275$ TYPE%main!nl_basics.Elem.)
        )
        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem.
            (main!nl_basics.sub_.? x~271$ y~273$)
           ) z~275$
          )
         ) (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
             x~271$ z~275$
            )
           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? y~273$ z~275$))
       ))))
       :pattern ((main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? x~271$
           y~273$
          )
         ) z~275$
       ))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_6
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_6
     ))
     (forall ((x~321$ Poly) (y~323$ Poly) (m~325$ Poly)) (!
       (=>
        (and
         (has_type x~321$ TYPE%main!nl_basics.Elem.)
         (has_type y~323$ TYPE%main!nl_basics.Elem.)
         (has_type m~325$ TYPE%main!nl_basics.Elem.)
        )
        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem.
            (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? x~321$ y~323$))
             m~325$
            )
           ) m~325$
          )
         ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
             (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? x~321$ m~325$)) (Poly%main!nl_basics.Elem.
              (main!nl_basics.mod_.? y~323$ m~325$)
            ))
           ) m~325$
       ))))
       :pattern ((main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem.
            (main!nl_basics.mul_.? x~321$ y~323$)
           ) m~325$
          )
         ) m~325$
       ))
       :pattern ((main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? x~321$
           m~325$
          )
         ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? y~323$ m~325$))
       ))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_7
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_7
     ))
     (forall ((x~381$ Poly) (y~383$ Poly) (m~385$ Poly)) (!
       (=>
        (and
         (has_type x~381$ TYPE%main!nl_basics.Elem.)
         (has_type y~383$ TYPE%main!nl_basics.Elem.)
         (has_type m~385$ TYPE%main!nl_basics.Elem.)
        )
        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem.
            (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? x~381$ y~383$))
             m~385$
            )
           ) m~385$
          )
         ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
             x~381$ (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? y~383$ m~385$))
            )
           ) m~385$
       ))))
       :pattern ((main!nl_basics.mul_.? x~381$ (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
           y~383$ m~385$
       ))))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_8
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_8
     ))
     (forall ((x~436$ Poly) (y~438$ Poly) (m~440$ Poly)) (!
       (=>
        (and
         (has_type x~436$ TYPE%main!nl_basics.Elem.)
         (has_type y~438$ TYPE%main!nl_basics.Elem.)
         (has_type m~440$ TYPE%main!nl_basics.Elem.)
        )
        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem.
            (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? x~436$ y~438$))
             m~440$
            )
           ) m~440$
          )
         ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
             y~438$ (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? x~436$ m~440$))
            )
           ) m~440$
       ))))
       :pattern ((main!nl_basics.mul_.? y~438$ (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
           x~436$ m~440$
       ))))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_9
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_9
     ))
     (forall ((x~491$ Poly) (y~493$ Poly) (m~495$ Poly)) (!
       (=>
        (and
         (has_type x~491$ TYPE%main!nl_basics.Elem.)
         (has_type y~493$ TYPE%main!nl_basics.Elem.)
         (has_type m~495$ TYPE%main!nl_basics.Elem.)
        )
        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? x~491$ m~495$))
         (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
             x~491$ (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? y~493$ m~495$))
            )
           ) m~495$
       ))))
       :pattern ((main!nl_basics.add_.? x~491$ (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
           y~493$ m~495$
       ))))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_10
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_10
     ))
     (forall ((x~536$ Poly) (y~538$ Poly) (m~540$ Poly)) (!
       (=>
        (and
         (has_type x~536$ TYPE%main!nl_basics.Elem.)
         (has_type y~538$ TYPE%main!nl_basics.Elem.)
         (has_type m~540$ TYPE%main!nl_basics.Elem.)
        )
        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? x~536$ m~540$))
         (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
             (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? y~538$ m~540$)) x~536$
            )
           ) m~540$
       ))))
       :pattern ((main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? y~538$
           m~540$
          )
         ) x~536$
       ))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_11
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_11
     ))
     (forall ((x~581$ Poly) (y~583$ Poly) (m~585$ Poly)) (!
       (=>
        (and
         (has_type x~581$ TYPE%main!nl_basics.Elem.)
         (has_type y~583$ TYPE%main!nl_basics.Elem.)
         (has_type m~585$ TYPE%main!nl_basics.Elem.)
        )
        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? x~581$ m~585$))
         (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
             x~581$ (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? y~583$ m~585$))
            )
           ) m~585$
       ))))
       :pattern ((main!nl_basics.sub_.? x~581$ (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
           y~583$ m~585$
       ))))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_12
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_12
     ))
     (forall ((x~626$ Poly) (y~628$ Poly) (m~630$ Poly)) (!
       (=>
        (and
         (has_type x~626$ TYPE%main!nl_basics.Elem.)
         (has_type y~628$ TYPE%main!nl_basics.Elem.)
         (has_type m~630$ TYPE%main!nl_basics.Elem.)
        )
        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem.
            (main!nl_basics.add_.? x~626$ y~628$)
           ) m~630$
          )
         ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
             (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? x~626$ m~630$)) (Poly%main!nl_basics.Elem.
              (main!nl_basics.mod_.? y~628$ m~630$)
            ))
           ) m~630$
       ))))
       :pattern ((main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? x~626$
           m~630$
          )
         ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? y~628$ m~630$))
       ))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_13
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_13
     ))
     (forall ((x~681$ Poly) (y~683$ Poly) (m~685$ Poly)) (!
       (=>
        (and
         (has_type x~681$ TYPE%main!nl_basics.Elem.)
         (has_type y~683$ TYPE%main!nl_basics.Elem.)
         (has_type m~685$ TYPE%main!nl_basics.Elem.)
        )
        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem.
            (main!nl_basics.add_.? x~681$ y~683$)
           ) m~685$
          )
         ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
             x~681$ (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? y~683$ m~685$))
            )
           ) m~685$
       ))))
       :pattern ((main!nl_basics.add_.? x~681$ (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
           y~683$ m~685$
       ))))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_14
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_14
     ))
     (forall ((x~731$ Poly) (y~733$ Poly) (m~735$ Poly)) (!
       (=>
        (and
         (has_type x~731$ TYPE%main!nl_basics.Elem.)
         (has_type y~733$ TYPE%main!nl_basics.Elem.)
         (has_type m~735$ TYPE%main!nl_basics.Elem.)
        )
        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem.
            (main!nl_basics.add_.? x~731$ y~733$)
           ) m~735$
          )
         ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
             (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? x~731$ m~735$)) y~733$
            )
           ) m~735$
       ))))
       :pattern ((main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? x~731$
           m~735$
          )
         ) y~733$
       ))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_15
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_15
     ))
     (forall ((x~781$ Poly) (y~783$ Poly) (m~785$ Poly)) (!
       (=>
        (and
         (has_type x~781$ TYPE%main!nl_basics.Elem.)
         (has_type y~783$ TYPE%main!nl_basics.Elem.)
         (has_type m~785$ TYPE%main!nl_basics.Elem.)
        )
        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem.
            (main!nl_basics.sub_.? x~781$ y~783$)
           ) m~785$
          )
         ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
             (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? x~781$ m~785$)) (Poly%main!nl_basics.Elem.
              (main!nl_basics.mod_.? y~783$ m~785$)
            ))
           ) m~785$
       ))))
       :pattern ((main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? x~781$
           m~785$
          )
         ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? y~783$ m~785$))
       ))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_16
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_16
     ))
     (forall ((x~836$ Poly) (y~838$ Poly) (m~840$ Poly)) (!
       (=>
        (and
         (has_type x~836$ TYPE%main!nl_basics.Elem.)
         (has_type y~838$ TYPE%main!nl_basics.Elem.)
         (has_type m~840$ TYPE%main!nl_basics.Elem.)
        )
        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem.
            (main!nl_basics.sub_.? x~836$ y~838$)
           ) m~840$
          )
         ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
             x~836$ (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? y~838$ m~840$))
            )
           ) m~840$
       ))))
       :pattern ((main!nl_basics.sub_.? x~836$ (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
           y~838$ m~840$
       ))))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_17
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_17
     ))
     (forall ((x~886$ Poly) (y~888$ Poly) (m~890$ Poly)) (!
       (=>
        (and
         (has_type x~886$ TYPE%main!nl_basics.Elem.)
         (has_type y~888$ TYPE%main!nl_basics.Elem.)
         (has_type m~890$ TYPE%main!nl_basics.Elem.)
        )
        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem.
            (main!nl_basics.sub_.? x~886$ y~888$)
           ) m~890$
          )
         ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
             (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? x~886$ m~890$)) y~888$
            )
           ) m~890$
       ))))
       :pattern ((main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? x~886$
           m~890$
          )
         ) y~888$
       ))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_18
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_18
     ))
     (forall ((x~936$ Poly)) (!
       (=>
        (has_type x~936$ TYPE%main!nl_basics.Elem.)
        (main!nl_basics.eq_.? x~936$ x~936$)
       )
       :pattern ((main!nl_basics.eq_.? x~936$ x~936$))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_19
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_19
     ))
     (forall ((x~953$ Poly) (y~955$ Poly)) (!
       (=>
        (and
         (has_type x~953$ TYPE%main!nl_basics.Elem.)
         (has_type y~955$ TYPE%main!nl_basics.Elem.)
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
         (has_type x~986$ TYPE%main!nl_basics.Elem.)
         (has_type y~988$ TYPE%main!nl_basics.Elem.)
         (has_type z~990$ TYPE%main!nl_basics.Elem.)
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
         (has_type x0~1031$ TYPE%main!nl_basics.Elem.)
         (has_type y0~1033$ TYPE%main!nl_basics.Elem.)
         (has_type x1~1035$ TYPE%main!nl_basics.Elem.)
         (has_type y1~1037$ TYPE%main!nl_basics.Elem.)
        )
        (=>
         (and
          (main!nl_basics.eq_.? x0~1031$ x1~1035$)
          (main!nl_basics.eq_.? y0~1033$ y1~1037$)
         )
         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? x0~1031$ y0~1033$))
          (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? x1~1035$ y1~1037$))
       )))
       :pattern ((main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? x0~1031$
           y0~1033$
          )
         ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? x1~1035$ y1~1037$))
       ))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_22
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_22
     ))
     (forall ((x0~1090$ Poly) (y0~1092$ Poly) (x1~1094$ Poly) (y1~1096$ Poly)) (!
       (=>
        (and
         (has_type x0~1090$ TYPE%main!nl_basics.Elem.)
         (has_type y0~1092$ TYPE%main!nl_basics.Elem.)
         (has_type x1~1094$ TYPE%main!nl_basics.Elem.)
         (has_type y1~1096$ TYPE%main!nl_basics.Elem.)
        )
        (=>
         (and
          (main!nl_basics.eq_.? x0~1090$ x1~1094$)
          (main!nl_basics.eq_.? y0~1092$ y1~1096$)
         )
         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? x0~1090$ y0~1092$))
          (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? x1~1094$ y1~1096$))
       )))
       :pattern ((main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? x0~1090$
           y0~1092$
          )
         ) (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? x1~1094$ y1~1096$))
       ))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_23
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_23
     ))
     (forall ((x0~1149$ Poly) (y0~1151$ Poly) (x1~1153$ Poly) (y1~1155$ Poly)) (!
       (=>
        (and
         (has_type x0~1149$ TYPE%main!nl_basics.Elem.)
         (has_type y0~1151$ TYPE%main!nl_basics.Elem.)
         (has_type x1~1153$ TYPE%main!nl_basics.Elem.)
         (has_type y1~1155$ TYPE%main!nl_basics.Elem.)
        )
        (=>
         (and
          (main!nl_basics.eq_.? x0~1149$ x1~1153$)
          (main!nl_basics.eq_.? y0~1151$ y1~1155$)
         )
         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? x0~1149$ y0~1151$))
          (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? x1~1153$ y1~1155$))
       )))
       :pattern ((main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? x0~1149$
           y0~1151$
          )
         ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? x1~1153$ y1~1155$))
       ))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_24
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_24
     ))
     (forall ((x0~1208$ Poly) (y0~1210$ Poly) (x1~1212$ Poly) (y1~1214$ Poly)) (!
       (=>
        (and
         (has_type x0~1208$ TYPE%main!nl_basics.Elem.)
         (has_type y0~1210$ TYPE%main!nl_basics.Elem.)
         (has_type x1~1212$ TYPE%main!nl_basics.Elem.)
         (has_type y1~1214$ TYPE%main!nl_basics.Elem.)
        )
        (=>
         (and
          (main!nl_basics.eq_.? x0~1208$ x1~1212$)
          (main!nl_basics.eq_.? y0~1210$ y1~1214$)
         )
         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? x0~1208$ y0~1210$))
          (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? x1~1212$ y1~1214$))
       )))
       :pattern ((main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? x0~1208$
           y0~1210$
          )
         ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? x1~1212$ y1~1214$))
       ))
       :qid user_main__nl_basics__lemma_mul_properties_auto_1_25
       :skolemid skolem_user_main__nl_basics__lemma_mul_properties_auto_1_25
   ))))
   :pattern ((ens%main!nl_basics.lemma_mul_properties_auto_1. no%param@))
   :qid internal_ens__main!nl_basics.lemma_mul_properties_auto_1._definition
   :skolemid skolem_internal_ens__main!nl_basics.lemma_mul_properties_auto_1._definition
)))

;; Function-Def main::auto_0
;; mariposa_data/uf//1571068856706693156/nlqi_verus/src/main.rs:7:1: 7:65 (#0)
(push)
 (declare-const a~2@ main!nl_basics.Elem.)
 (declare-const b~4@ main!nl_basics.Elem.)
 (declare-const c~6@ main!nl_basics.Elem.)
 (declare-const d~8@ main!nl_basics.Elem.)
 (declare-const m~10@ main!nl_basics.Elem.)
 (declare-const temp_0_0~30@ main!nl_basics.Elem.)
 (declare-const temp_0_1~50@ main!nl_basics.Elem.)
 (declare-const temp_1_0~92@ main!nl_basics.Elem.)
 (declare-const temp_1_1~112@ main!nl_basics.Elem.)
 (declare-const temp_2_0~154@ main!nl_basics.Elem.)
 (declare-const temp_2_1~174@ main!nl_basics.Elem.)
 (declare-const temp_3_0~221@ main!nl_basics.Elem.)
 (declare-const temp_3_1~246@ main!nl_basics.Elem.)
 (declare-const temp_4_0~288@ main!nl_basics.Elem.)
 (declare-const temp_4_1~308@ main!nl_basics.Elem.)
 (declare-const temp_5_0~355@ main!nl_basics.Elem.)
 (declare-const temp_5_1~380@ main!nl_basics.Elem.)
 (declare-const temp_6_0~427@ main!nl_basics.Elem.)
 (declare-const temp_6_1~452@ main!nl_basics.Elem.)
 (declare-const temp_7_0~494@ main!nl_basics.Elem.)
 (declare-const temp_7_1~514@ main!nl_basics.Elem.)
 (declare-const temp_8_0~561@ main!nl_basics.Elem.)
 (declare-const temp_8_1~616@ main!nl_basics.Elem.)
 (declare-const temp_9_0~658@ main!nl_basics.Elem.)
 (declare-const temp_9_1~678@ main!nl_basics.Elem.)
 (declare-const temp_10_0~725@ main!nl_basics.Elem.)
 (declare-const temp_10_1~785@ main!nl_basics.Elem.)
 (declare-const temp_11_0~832@ main!nl_basics.Elem.)
 (declare-const temp_11_1~887@ main!nl_basics.Elem.)
 (declare-const temp_12_0~929@ main!nl_basics.Elem.)
 (declare-const temp_12_1~949@ main!nl_basics.Elem.)
 (declare-const temp_13_0~1001@ main!nl_basics.Elem.)
 (declare-const temp_13_1~1031@ main!nl_basics.Elem.)
 (declare-const temp_14_0~1087@ main!nl_basics.Elem.)
 (declare-const temp_14_1~1121@ main!nl_basics.Elem.)
 (declare-const temp_15_0~1168@ main!nl_basics.Elem.)
 (declare-const temp_15_1~1223@ main!nl_basics.Elem.)
 (declare-const temp_16_0~1270@ main!nl_basics.Elem.)
 (declare-const temp_16_1~1295@ main!nl_basics.Elem.)
 (declare-const temp_17_0~1342@ main!nl_basics.Elem.)
 (declare-const temp_17_1~1367@ main!nl_basics.Elem.)
 (declare-const temp_18_0~1409@ main!nl_basics.Elem.)
 (declare-const temp_18_1~1429@ main!nl_basics.Elem.)
 (declare-const temp_19_0~1478@ main!nl_basics.Elem.)
 (declare-const temp_19_1~1505@ main!nl_basics.Elem.)
 (declare-const temp_20_0~1557@ main!nl_basics.Elem.)
 (declare-const temp_20_1~1622@ main!nl_basics.Elem.)
 (declare-const temp_21_0~1664@ main!nl_basics.Elem.)
 (declare-const temp_21_1~1684@ main!nl_basics.Elem.)
 (declare-const temp_22_0~1731@ main!nl_basics.Elem.)
 (declare-const temp_22_1~1756@ main!nl_basics.Elem.)
 (declare-const temp_23_0~1798@ main!nl_basics.Elem.)
 (declare-const temp_23_1~1818@ main!nl_basics.Elem.)
 (declare-const temp_24_0~1870@ main!nl_basics.Elem.)
 (declare-const temp_24_1~1930@ main!nl_basics.Elem.)
 (declare-const temp_25_0~1982@ main!nl_basics.Elem.)
 (declare-const temp_25_1~2012@ main!nl_basics.Elem.)
 (declare-const temp_26_0~2059@ main!nl_basics.Elem.)
 (declare-const temp_26_1~2109@ main!nl_basics.Elem.)
 (declare-const temp_27_0~2156@ main!nl_basics.Elem.)
 (declare-const temp_27_1~2181@ main!nl_basics.Elem.)
 (declare-const temp_28_0~2223@ main!nl_basics.Elem.)
 (declare-const temp_28_1~2243@ main!nl_basics.Elem.)
 (declare-const temp_29_0~2290@ main!nl_basics.Elem.)
 (declare-const temp_29_1~2315@ main!nl_basics.Elem.)
 (declare-const temp_30_0~2372@ main!nl_basics.Elem.)
 (declare-const temp_30_1~2407@ main!nl_basics.Elem.)
 (declare-const temp_31_0~2454@ main!nl_basics.Elem.)
 (declare-const temp_31_1~2504@ main!nl_basics.Elem.)
 (declare-const temp_32_0~2546@ main!nl_basics.Elem.)
 (declare-const temp_32_1~2566@ main!nl_basics.Elem.)
 (declare-const temp_33_0~2608@ main!nl_basics.Elem.)
 (declare-const temp_33_1~2628@ main!nl_basics.Elem.)
 (declare-const temp_34_0~2670@ main!nl_basics.Elem.)
 (declare-const temp_34_1~2690@ main!nl_basics.Elem.)
 (declare-const temp_35_0~2737@ main!nl_basics.Elem.)
 (declare-const temp_35_1~2797@ main!nl_basics.Elem.)
 (declare-const temp_36_0~2844@ main!nl_basics.Elem.)
 (declare-const temp_36_1~2869@ main!nl_basics.Elem.)
 (declare-const temp_37_0~2911@ main!nl_basics.Elem.)
 (declare-const temp_37_1~2931@ main!nl_basics.Elem.)
 (declare-const temp_38_0~2973@ main!nl_basics.Elem.)
 (declare-const temp_38_1~2993@ main!nl_basics.Elem.)
 (declare-const temp_39_0~3047@ main!nl_basics.Elem.)
 (declare-const temp_39_1~3101@ main!nl_basics.Elem.)
 (declare-const temp_40_0~3153@ main!nl_basics.Elem.)
 (declare-const temp_40_1~3218@ main!nl_basics.Elem.)
 (declare-const temp_41_0~3260@ main!nl_basics.Elem.)
 (declare-const temp_41_1~3280@ main!nl_basics.Elem.)
 (declare-const temp_42_0~3327@ main!nl_basics.Elem.)
 (declare-const temp_42_1~3391@ main!nl_basics.Elem.)
 (declare-const temp_43_0~3433@ main!nl_basics.Elem.)
 (declare-const temp_43_1~3463@ main!nl_basics.Elem.)
 (declare-const temp_44_0~3500@ main!nl_basics.Elem.)
 (declare-const temp_44_1~3515@ main!nl_basics.Elem.)
 (declare-const temp_45_0~3562@ main!nl_basics.Elem.)
 (declare-const temp_45_1~3587@ main!nl_basics.Elem.)
 (declare-const temp_46_0~3639@ main!nl_basics.Elem.)
 (declare-const temp_46_1~3669@ main!nl_basics.Elem.)
 (declare-const temp_47_0~3711@ main!nl_basics.Elem.)
 (declare-const temp_47_1~3731@ main!nl_basics.Elem.)
 (declare-const temp_48_0~3780@ main!nl_basics.Elem.)
 (declare-const temp_48_1~3837@ main!nl_basics.Elem.)
 (declare-const temp_49_0~3879@ main!nl_basics.Elem.)
 (declare-const temp_49_1~3899@ main!nl_basics.Elem.)
 (declare-const temp_50_0~3946@ main!nl_basics.Elem.)
 (declare-const temp_50_1~3981@ main!nl_basics.Elem.)
 (declare-const temp_51_0~4028@ main!nl_basics.Elem.)
 (declare-const temp_51_1~4068@ main!nl_basics.Elem.)
 (declare-const temp_52_0~4115@ main!nl_basics.Elem.)
 (declare-const temp_52_1~4140@ main!nl_basics.Elem.)
 (declare-const temp_53_0~4182@ main!nl_basics.Elem.)
 (declare-const temp_53_1~4202@ main!nl_basics.Elem.)
 (declare-const temp_54_0~4249@ main!nl_basics.Elem.)
 (declare-const temp_54_1~4299@ main!nl_basics.Elem.)
 (declare-const temp_55_0~4346@ main!nl_basics.Elem.)
 (declare-const temp_55_1~4396@ main!nl_basics.Elem.)
 (declare-const temp_56_0~4443@ main!nl_basics.Elem.)
 (declare-const temp_56_1~4468@ main!nl_basics.Elem.)
 (declare-const temp_57_0~4510@ main!nl_basics.Elem.)
 (declare-const temp_57_1~4530@ main!nl_basics.Elem.)
 (declare-const temp_58_0~4592@ main!nl_basics.Elem.)
 (declare-const temp_58_1~4632@ main!nl_basics.Elem.)
 (declare-const temp_59_0~4679@ main!nl_basics.Elem.)
 (declare-const temp_59_1~4704@ main!nl_basics.Elem.)
 (declare-const temp_60_0~4746@ main!nl_basics.Elem.)
 (declare-const temp_60_1~4766@ main!nl_basics.Elem.)
 (declare-const temp_61_0~4813@ main!nl_basics.Elem.)
 (declare-const temp_61_1~4838@ main!nl_basics.Elem.)
 (declare-const temp_62_0~4890@ main!nl_basics.Elem.)
 (declare-const temp_62_1~4920@ main!nl_basics.Elem.)
 (declare-const temp_63_0~4972@ main!nl_basics.Elem.)
 (declare-const temp_63_1~5032@ main!nl_basics.Elem.)
 (declare-const temp_64_0~5074@ main!nl_basics.Elem.)
 (declare-const temp_64_1~5094@ main!nl_basics.Elem.)
 (declare-const temp_65_0~5136@ main!nl_basics.Elem.)
 (declare-const temp_65_1~5156@ main!nl_basics.Elem.)
 (declare-const temp_66_0~5203@ main!nl_basics.Elem.)
 (declare-const temp_66_1~5228@ main!nl_basics.Elem.)
 (declare-const temp_67_0~5270@ main!nl_basics.Elem.)
 (declare-const temp_67_1~5290@ main!nl_basics.Elem.)
 (declare-const temp_68_0~5337@ main!nl_basics.Elem.)
 (declare-const temp_68_1~5397@ main!nl_basics.Elem.)
 (declare-const temp_69_0~5449@ main!nl_basics.Elem.)
 (declare-const temp_69_1~5479@ main!nl_basics.Elem.)
 (declare-const temp_70_0~5521@ main!nl_basics.Elem.)
 (declare-const temp_70_1~5541@ main!nl_basics.Elem.)
 (declare-const temp_71_0~5583@ main!nl_basics.Elem.)
 (declare-const temp_71_1~5603@ main!nl_basics.Elem.)
 (declare-const temp_72_0~5645@ main!nl_basics.Elem.)
 (declare-const temp_72_1~5665@ main!nl_basics.Elem.)
 (declare-const temp_73_0~5712@ main!nl_basics.Elem.)
 (declare-const temp_73_1~5737@ main!nl_basics.Elem.)
 (declare-const temp_74_0~5779@ main!nl_basics.Elem.)
 (declare-const temp_74_1~5799@ main!nl_basics.Elem.)
 (declare-const temp_75_0~5851@ main!nl_basics.Elem.)
 (declare-const temp_75_1~5881@ main!nl_basics.Elem.)
 (declare-const temp_76_0~5933@ main!nl_basics.Elem.)
 (declare-const temp_76_1~5963@ main!nl_basics.Elem.)
 (declare-const temp_77_0~6010@ main!nl_basics.Elem.)
 (declare-const temp_77_1~6060@ main!nl_basics.Elem.)
 (declare-const temp_78_0~6102@ main!nl_basics.Elem.)
 (declare-const temp_78_1~6122@ main!nl_basics.Elem.)
 (declare-const temp_79_0~6174@ main!nl_basics.Elem.)
 (declare-const temp_79_1~6234@ main!nl_basics.Elem.)
 (declare-const temp_80_0~6276@ main!nl_basics.Elem.)
 (declare-const temp_80_1~6296@ main!nl_basics.Elem.)
 (declare-const temp_81_0~6348@ main!nl_basics.Elem.)
 (declare-const temp_81_1~6408@ main!nl_basics.Elem.)
 (declare-const temp_82_0~6455@ main!nl_basics.Elem.)
 (declare-const temp_82_1~6510@ main!nl_basics.Elem.)
 (declare-const temp_83_0~6552@ main!nl_basics.Elem.)
 (declare-const temp_83_1~6572@ main!nl_basics.Elem.)
 (declare-const temp_84_0~6624@ main!nl_basics.Elem.)
 (declare-const temp_84_1~6684@ main!nl_basics.Elem.)
 (declare-const temp_85_0~6736@ main!nl_basics.Elem.)
 (declare-const temp_85_1~6766@ main!nl_basics.Elem.)
 (declare-const temp_86_0~6813@ main!nl_basics.Elem.)
 (declare-const temp_86_1~6838@ main!nl_basics.Elem.)
 (declare-const temp_87_0~6890@ main!nl_basics.Elem.)
 (declare-const temp_87_1~6955@ main!nl_basics.Elem.)
 (declare-const temp_88_0~7004@ main!nl_basics.Elem.)
 (declare-const temp_88_1~7031@ main!nl_basics.Elem.)
 (declare-const temp_89_0~7073@ main!nl_basics.Elem.)
 (declare-const temp_89_1~7093@ main!nl_basics.Elem.)
 (declare-const temp_90_0~7145@ main!nl_basics.Elem.)
 (declare-const temp_90_1~7200@ main!nl_basics.Elem.)
 (declare-const temp_91_0~7249@ main!nl_basics.Elem.)
 (declare-const temp_91_1~7276@ main!nl_basics.Elem.)
 (declare-const temp_92_0~7318@ main!nl_basics.Elem.)
 (declare-const temp_92_1~7338@ main!nl_basics.Elem.)
 (declare-const temp_93_0~7380@ main!nl_basics.Elem.)
 (declare-const temp_93_1~7400@ main!nl_basics.Elem.)
 (declare-const temp_94_0~7444@ main!nl_basics.Elem.)
 (declare-const temp_94_1~7466@ main!nl_basics.Elem.)
 (declare-const temp_95_0~7513@ main!nl_basics.Elem.)
 (declare-const temp_95_1~7553@ main!nl_basics.Elem.)
 (declare-const temp_96_0~7595@ main!nl_basics.Elem.)
 (declare-const temp_96_1~7615@ main!nl_basics.Elem.)
 (declare-const temp_97_0~7667@ main!nl_basics.Elem.)
 (declare-const temp_97_1~7697@ main!nl_basics.Elem.)
 (declare-const temp_98_0~7751@ main!nl_basics.Elem.)
 (declare-const temp_98_1~7783@ main!nl_basics.Elem.)
 (declare-const temp_99_0~7825@ main!nl_basics.Elem.)
 (declare-const temp_99_1~7845@ main!nl_basics.Elem.)
 (declare-const temp_100_0~7887@ main!nl_basics.Elem.)
 (declare-const temp_100_1~7907@ main!nl_basics.Elem.)
 (declare-const temp_101_0~7954@ main!nl_basics.Elem.)
 (declare-const temp_101_1~7979@ main!nl_basics.Elem.)
 (declare-const temp_102_0~8028@ main!nl_basics.Elem.)
 (declare-const temp_102_1~8055@ main!nl_basics.Elem.)
 (declare-const temp_103_0~8102@ main!nl_basics.Elem.)
 (declare-const temp_103_1~8127@ main!nl_basics.Elem.)
 (declare-const temp_104_0~8179@ main!nl_basics.Elem.)
 (declare-const temp_104_1~8209@ main!nl_basics.Elem.)
 (declare-const temp_105_0~8256@ main!nl_basics.Elem.)
 (declare-const temp_105_1~8281@ main!nl_basics.Elem.)
 (declare-const temp_106_0~8318@ main!nl_basics.Elem.)
 (declare-const temp_106_1~8333@ main!nl_basics.Elem.)
 (declare-const temp_107_0~8380@ main!nl_basics.Elem.)
 (declare-const temp_107_1~8430@ main!nl_basics.Elem.)
 (declare-const temp_108_0~8472@ main!nl_basics.Elem.)
 (declare-const temp_108_1~8492@ main!nl_basics.Elem.)
 (declare-const temp_109_0~8539@ main!nl_basics.Elem.)
 (declare-const temp_109_1~8589@ main!nl_basics.Elem.)
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
 ;; assertion failed
 (declare-const %%location_label%%100 Bool)
 ;; assertion failed
 (declare-const %%location_label%%101 Bool)
 ;; assertion failed
 (declare-const %%location_label%%102 Bool)
 ;; assertion failed
 (declare-const %%location_label%%103 Bool)
 ;; assertion failed
 (declare-const %%location_label%%104 Bool)
 ;; assertion failed
 (declare-const %%location_label%%105 Bool)
 ;; assertion failed
 (declare-const %%location_label%%106 Bool)
 ;; assertion failed
 (declare-const %%location_label%%107 Bool)
 ;; assertion failed
 (declare-const %%location_label%%108 Bool)
 ;; assertion failed
 (declare-const %%location_label%%109 Bool)
 (declare-const %%query%% Bool)
 (assert
  (=>
   %%query%%
   (not (=>
     (= temp_0_0~30@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
         (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. b~4@)
        )
       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
         (Poly%main!nl_basics.Elem. c~6@)
     ))))
     (=>
      (= temp_0_1~50@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem.
         (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem.
           (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem.
             c~6@
      )))))))
      (and
       (=>
        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
        (=>
         %%location_label%%0
         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_0_0~30@) (Poly%main!nl_basics.Elem.
           temp_0_1~50@
       ))))
       (=>
        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_0_0~30@) (Poly%main!nl_basics.Elem.
          temp_0_1~50@
        ))
        (=>
         (= temp_1_0~92@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
             (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. d~8@)
            )
           ) (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. a~2@)
             (Poly%main!nl_basics.Elem. c~6@)
         ))))
         (=>
          (= temp_1_1~112@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
              (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. c~6@)
             )
            ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
              (Poly%main!nl_basics.Elem. d~8@)
          ))))
          (and
           (=>
            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
            (=>
             %%location_label%%1
             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_1_0~92@) (Poly%main!nl_basics.Elem.
               temp_1_1~112@
           ))))
           (=>
            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_1_0~92@) (Poly%main!nl_basics.Elem.
              temp_1_1~112@
            ))
            (=>
             (= temp_2_0~154@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                 (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. d~8@)
                )
               ) (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. b~4@)
                 (Poly%main!nl_basics.Elem. a~2@)
             ))))
             (=>
              (= temp_2_1~174@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                  (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. b~4@)
                 )
                ) (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. b~4@)
                  (Poly%main!nl_basics.Elem. a~2@)
              ))))
              (and
               (=>
                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                (=>
                 %%location_label%%2
                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_2_0~154@) (Poly%main!nl_basics.Elem.
                   temp_2_1~174@
               ))))
               (=>
                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_2_0~154@) (Poly%main!nl_basics.Elem.
                  temp_2_1~174@
                ))
                (=>
                 (= temp_3_0~221@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                     (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                       (Poly%main!nl_basics.Elem. a~2@)
                      )
                     ) (Poly%main!nl_basics.Elem. m~10@)
                    )
                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                     (Poly%main!nl_basics.Elem. a~2@)
                 ))))
                 (=>
                  (= temp_3_1~246@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                      (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                        (Poly%main!nl_basics.Elem. b~4@)
                       )
                      ) (Poly%main!nl_basics.Elem. m~10@)
                     )
                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                      (Poly%main!nl_basics.Elem. a~2@)
                  ))))
                  (and
                   (=>
                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                    (=>
                     %%location_label%%3
                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_3_0~221@) (Poly%main!nl_basics.Elem.
                       temp_3_1~246@
                   ))))
                   (=>
                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_3_0~221@) (Poly%main!nl_basics.Elem.
                      temp_3_1~246@
                    ))
                    (=>
                     (= temp_4_0~288@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                         (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. a~2@)
                        )
                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. b~4@)
                         (Poly%main!nl_basics.Elem. b~4@)
                     ))))
                     (=>
                      (= temp_4_1~308@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                          (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. b~4@)
                         )
                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                          (Poly%main!nl_basics.Elem. a~2@)
                      ))))
                      (and
                       (=>
                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                        (=>
                         %%location_label%%4
                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_4_0~288@) (Poly%main!nl_basics.Elem.
                           temp_4_1~308@
                       ))))
                       (=>
                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_4_0~288@) (Poly%main!nl_basics.Elem.
                          temp_4_1~308@
                        ))
                        (=>
                         (= temp_5_0~355@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                             (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                               (Poly%main!nl_basics.Elem. a~2@)
                              )
                             ) (Poly%main!nl_basics.Elem. m~10@)
                            )
                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                             (Poly%main!nl_basics.Elem. d~8@)
                         ))))
                         (=>
                          (= temp_5_1~380@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                              (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                  (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. a~2@)
                                 )
                                ) (Poly%main!nl_basics.Elem. m~10@)
                               )
                              ) (Poly%main!nl_basics.Elem. a~2@)
                             )
                            ) (Poly%main!nl_basics.Elem. d~8@)
                          ))
                          (and
                           (=>
                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                            (=>
                             %%location_label%%5
                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_5_0~355@) (Poly%main!nl_basics.Elem.
                               temp_5_1~380@
                           ))))
                           (=>
                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_5_0~355@) (Poly%main!nl_basics.Elem.
                              temp_5_1~380@
                            ))
                            (=>
                             (= temp_6_0~427@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                 (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. c~6@)
                                )
                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                 (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. b~4@)
                                   (Poly%main!nl_basics.Elem. m~10@)
                             ))))))
                             (=>
                              (= temp_6_1~452@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                  (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. c~6@)
                                 )
                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                    (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. m~10@)
                                   )
                                  ) (Poly%main!nl_basics.Elem. a~2@)
                              ))))
                              (and
                               (=>
                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                (=>
                                 %%location_label%%6
                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_6_0~427@) (Poly%main!nl_basics.Elem.
                                   temp_6_1~452@
                               ))))
                               (=>
                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_6_0~427@) (Poly%main!nl_basics.Elem.
                                  temp_6_1~452@
                                ))
                                (=>
                                 (= temp_7_0~494@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                     (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. c~6@)
                                    )
                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                     (Poly%main!nl_basics.Elem. a~2@)
                                 ))))
                                 (=>
                                  (= temp_7_1~514@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                      (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. a~2@)
                                     )
                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                      (Poly%main!nl_basics.Elem. c~6@)
                                  ))))
                                  (and
                                   (=>
                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                    (=>
                                     %%location_label%%7
                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_7_0~494@) (Poly%main!nl_basics.Elem.
                                       temp_7_1~514@
                                   ))))
                                   (=>
                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_7_0~494@) (Poly%main!nl_basics.Elem.
                                      temp_7_1~514@
                                    ))
                                    (=>
                                     (= temp_8_0~561@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                         (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. d~8@)
                                           (Poly%main!nl_basics.Elem. m~10@)
                                          )
                                         ) (Poly%main!nl_basics.Elem. a~2@)
                                        )
                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                         (Poly%main!nl_basics.Elem. b~4@)
                                     ))))
                                     (=>
                                      (= temp_8_1~616@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                          (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                              (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                  (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                    (Poly%main!nl_basics.Elem. b~4@)
                                                   )
                                                  ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                      (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. b~4@)
                                                     )
                                                    ) (Poly%main!nl_basics.Elem. m~10@)
                                                 )))
                                                ) (Poly%main!nl_basics.Elem. m~10@)
                                               )
                                              ) (Poly%main!nl_basics.Elem. d~8@)
                                             )
                                            ) (Poly%main!nl_basics.Elem. m~10@)
                                           )
                                          ) (Poly%main!nl_basics.Elem. a~2@)
                                         )
                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                          (Poly%main!nl_basics.Elem. b~4@)
                                      ))))
                                      (and
                                       (=>
                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                        (=>
                                         %%location_label%%8
                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_8_0~561@) (Poly%main!nl_basics.Elem.
                                           temp_8_1~616@
                                       ))))
                                       (=>
                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_8_0~561@) (Poly%main!nl_basics.Elem.
                                          temp_8_1~616@
                                        ))
                                        (=>
                                         (= temp_9_0~658@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                             (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. d~8@)
                                            )
                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                             (Poly%main!nl_basics.Elem. d~8@)
                                         ))))
                                         (=>
                                          (= temp_9_1~678@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem.
                                             (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem.
                                               (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem.
                                                 d~8@
                                          )))))))
                                          (and
                                           (=>
                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                            (=>
                                             %%location_label%%9
                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_9_0~658@) (Poly%main!nl_basics.Elem.
                                               temp_9_1~678@
                                           ))))
                                           (=>
                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_9_0~658@) (Poly%main!nl_basics.Elem.
                                              temp_9_1~678@
                                            ))
                                            (=>
                                             (= temp_10_0~725@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                 (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                   (Poly%main!nl_basics.Elem. a~2@)
                                                  )
                                                 ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                   (Poly%main!nl_basics.Elem. a~2@)
                                                )))
                                               ) (Poly%main!nl_basics.Elem. m~10@)
                                             ))
                                             (=>
                                              (= temp_10_1~785@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                  (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                      (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. a~2@)
                                                     )
                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                      (Poly%main!nl_basics.Elem. a~2@)
                                                   )))
                                                  ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                      (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. a~2@)
                                                        (Poly%main!nl_basics.Elem. b~4@)
                                                       )
                                                      ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                          (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. m~10@)
                                                         )
                                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. c~6@)
                                                          (Poly%main!nl_basics.Elem. m~10@)
                                                     )))))
                                                    ) (Poly%main!nl_basics.Elem. m~10@)
                                                 )))
                                                ) (Poly%main!nl_basics.Elem. m~10@)
                                              ))
                                              (and
                                               (=>
                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                (=>
                                                 %%location_label%%10
                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_10_0~725@) (Poly%main!nl_basics.Elem.
                                                   temp_10_1~785@
                                               ))))
                                               (=>
                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_10_0~725@) (Poly%main!nl_basics.Elem.
                                                  temp_10_1~785@
                                                ))
                                                (=>
                                                 (= temp_11_0~832@ (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                     (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. c~6@)
                                                    )
                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. d~8@)
                                                     (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. a~2@)
                                                       (Poly%main!nl_basics.Elem. m~10@)
                                                 ))))))
                                                 (=>
                                                  (= temp_11_1~887@ (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                      (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. c~6@)
                                                     )
                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. d~8@)
                                                      (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                          (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                              (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                  (Poly%main!nl_basics.Elem. m~10@)
                                                               )))
                                                              ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                (Poly%main!nl_basics.Elem. c~6@)
                                                             )))
                                                            ) (Poly%main!nl_basics.Elem. m~10@)
                                                           )
                                                          ) (Poly%main!nl_basics.Elem. a~2@)
                                                         )
                                                        ) (Poly%main!nl_basics.Elem. m~10@)
                                                  ))))))
                                                  (and
                                                   (=>
                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                    (=>
                                                     %%location_label%%11
                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_11_0~832@) (Poly%main!nl_basics.Elem.
                                                       temp_11_1~887@
                                                   ))))
                                                   (=>
                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_11_0~832@) (Poly%main!nl_basics.Elem.
                                                      temp_11_1~887@
                                                    ))
                                                    (=>
                                                     (= temp_12_0~929@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                         (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. c~6@)
                                                        )
                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                         (Poly%main!nl_basics.Elem. c~6@)
                                                     ))))
                                                     (=>
                                                      (= temp_12_1~949@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                          (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. c~6@)
                                                         )
                                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                          (Poly%main!nl_basics.Elem. c~6@)
                                                      ))))
                                                      (and
                                                       (=>
                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                        (=>
                                                         %%location_label%%12
                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_12_0~929@) (Poly%main!nl_basics.Elem.
                                                           temp_12_1~949@
                                                       ))))
                                                       (=>
                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_12_0~929@) (Poly%main!nl_basics.Elem.
                                                          temp_12_1~949@
                                                        ))
                                                        (=>
                                                         (= temp_13_0~1001@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                             (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                 (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. c~6@)
                                                                )
                                                               ) (Poly%main!nl_basics.Elem. m~10@)
                                                              )
                                                             ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                               (Poly%main!nl_basics.Elem. d~8@)
                                                            )))
                                                           ) (Poly%main!nl_basics.Elem. m~10@)
                                                         ))
                                                         (=>
                                                          (= temp_13_1~1031@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                              (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                (Poly%main!nl_basics.Elem. d~8@)
                                                               )
                                                              ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                  (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. c~6@)
                                                                 )
                                                                ) (Poly%main!nl_basics.Elem. m~10@)
                                                             )))
                                                            ) (Poly%main!nl_basics.Elem. m~10@)
                                                          ))
                                                          (and
                                                           (=>
                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                            (=>
                                                             %%location_label%%13
                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_13_0~1001@) (Poly%main!nl_basics.Elem.
                                                               temp_13_1~1031@
                                                           ))))
                                                           (=>
                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_13_0~1001@) (Poly%main!nl_basics.Elem.
                                                              temp_13_1~1031@
                                                            ))
                                                            (=>
                                                             (= temp_14_0~1087@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                 (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. (main!nl_basics.as_elem.?
                                                                   (I 93)
                                                                )))
                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.as_elem.?
                                                                   (I 69)
                                                                  )
                                                                 ) (Poly%main!nl_basics.Elem. b~4@)
                                                             ))))
                                                             (=>
                                                              (= temp_14_1~1121@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                  (Poly%main!nl_basics.Elem. (main!nl_basics.as_elem.? (I 93))) (Poly%main!nl_basics.Elem.
                                                                   c~6@
                                                                 ))
                                                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.as_elem.?
                                                                    (I 69)
                                                                   )
                                                                  ) (Poly%main!nl_basics.Elem. b~4@)
                                                              ))))
                                                              (and
                                                               (=>
                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                (=>
                                                                 %%location_label%%14
                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_14_0~1087@) (Poly%main!nl_basics.Elem.
                                                                   temp_14_1~1121@
                                                               ))))
                                                               (=>
                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_14_0~1087@) (Poly%main!nl_basics.Elem.
                                                                  temp_14_1~1121@
                                                                ))
                                                                (=>
                                                                 (= temp_15_0~1168@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                     (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                       (Poly%main!nl_basics.Elem. a~2@)
                                                                      )
                                                                     ) (Poly%main!nl_basics.Elem. m~10@)
                                                                    )
                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                     (Poly%main!nl_basics.Elem. a~2@)
                                                                 ))))
                                                                 (=>
                                                                  (= temp_15_1~1223@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                      (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                          (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. a~2@)
                                                                         )
                                                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                            (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. d~8@)
                                                                               )
                                                                              ) (Poly%main!nl_basics.Elem. m~10@)
                                                                             )
                                                                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                              (Poly%main!nl_basics.Elem. m~10@)
                                                                           )))
                                                                          ) (Poly%main!nl_basics.Elem. m~10@)
                                                                       )))
                                                                      ) (Poly%main!nl_basics.Elem. m~10@)
                                                                     )
                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                      (Poly%main!nl_basics.Elem. a~2@)
                                                                  ))))
                                                                  (and
                                                                   (=>
                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                    (=>
                                                                     %%location_label%%15
                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_15_0~1168@) (Poly%main!nl_basics.Elem.
                                                                       temp_15_1~1223@
                                                                   ))))
                                                                   (=>
                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_15_0~1168@) (Poly%main!nl_basics.Elem.
                                                                      temp_15_1~1223@
                                                                    ))
                                                                    (=>
                                                                     (= temp_16_0~1270@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                         (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. b~4@)
                                                                        )
                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                           (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. b~4@)
                                                                          )
                                                                         ) (Poly%main!nl_basics.Elem. m~10@)
                                                                     ))))
                                                                     (=>
                                                                      (= temp_16_1~1295@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                          (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. b~4@)
                                                                         )
                                                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                            (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. b~4@)
                                                                           )
                                                                          ) (Poly%main!nl_basics.Elem. m~10@)
                                                                      ))))
                                                                      (and
                                                                       (=>
                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                        (=>
                                                                         %%location_label%%16
                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_16_0~1270@) (Poly%main!nl_basics.Elem.
                                                                           temp_16_1~1295@
                                                                       ))))
                                                                       (=>
                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_16_0~1270@) (Poly%main!nl_basics.Elem.
                                                                          temp_16_1~1295@
                                                                        ))
                                                                        (=>
                                                                         (= temp_17_0~1342@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                             (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                               (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. m~10@)
                                                                            )))
                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                             (Poly%main!nl_basics.Elem. c~6@)
                                                                         ))))
                                                                         (=>
                                                                          (= temp_17_1~1367@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                              (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. m~10@)
                                                                             )))
                                                                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                              (Poly%main!nl_basics.Elem. a~2@)
                                                                          ))))
                                                                          (and
                                                                           (=>
                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                            (=>
                                                                             %%location_label%%17
                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_17_0~1342@) (Poly%main!nl_basics.Elem.
                                                                               temp_17_1~1367@
                                                                           ))))
                                                                           (=>
                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_17_0~1342@) (Poly%main!nl_basics.Elem.
                                                                              temp_17_1~1367@
                                                                            ))
                                                                            (=>
                                                                             (= temp_18_0~1409@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                 (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                )
                                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                 (Poly%main!nl_basics.Elem. c~6@)
                                                                             ))))
                                                                             (=>
                                                                              (= temp_18_1~1429@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                  (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                 )
                                                                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                  (Poly%main!nl_basics.Elem. a~2@)
                                                                              ))))
                                                                              (and
                                                                               (=>
                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                (=>
                                                                                 %%location_label%%18
                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_18_0~1409@) (Poly%main!nl_basics.Elem.
                                                                                   temp_18_1~1429@
                                                                               ))))
                                                                               (=>
                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_18_0~1409@) (Poly%main!nl_basics.Elem.
                                                                                  temp_18_1~1429@
                                                                                ))
                                                                                (=>
                                                                                 (= temp_19_0~1478@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                     (Poly%main!nl_basics.Elem. (main!nl_basics.as_elem.? (I 42))) (Poly%main!nl_basics.Elem.
                                                                                      d~8@
                                                                                    ))
                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                     (Poly%main!nl_basics.Elem. c~6@)
                                                                                 ))))
                                                                                 (=>
                                                                                  (= temp_19_1~1505@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                      (Poly%main!nl_basics.Elem. (main!nl_basics.as_elem.? (I 42))) (Poly%main!nl_basics.Elem.
                                                                                       d~8@
                                                                                     ))
                                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                      (Poly%main!nl_basics.Elem. d~8@)
                                                                                  ))))
                                                                                  (and
                                                                                   (=>
                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                    (=>
                                                                                     %%location_label%%19
                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_19_0~1478@) (Poly%main!nl_basics.Elem.
                                                                                       temp_19_1~1505@
                                                                                   ))))
                                                                                   (=>
                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_19_0~1478@) (Poly%main!nl_basics.Elem.
                                                                                      temp_19_1~1505@
                                                                                    ))
                                                                                    (=>
                                                                                     (= temp_20_0~1557@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                         (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                           (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                        )))
                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                           (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                          )
                                                                                         ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                     ))))
                                                                                     (=>
                                                                                      (= temp_20_1~1622@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                          (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                            (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                              (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                  (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                      (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                     )
                                                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                      (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                        (Poly%main!nl_basics.Elem. m~10@)
                                                                                                   )))))
                                                                                                  ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                 )
                                                                                                ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                             )))
                                                                                            ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                         )))
                                                                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                            (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                           )
                                                                                          ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                      ))))
                                                                                      (and
                                                                                       (=>
                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                        (=>
                                                                                         %%location_label%%20
                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_20_0~1557@) (Poly%main!nl_basics.Elem.
                                                                                           temp_20_1~1622@
                                                                                       ))))
                                                                                       (=>
                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_20_0~1557@) (Poly%main!nl_basics.Elem.
                                                                                          temp_20_1~1622@
                                                                                        ))
                                                                                        (=>
                                                                                         (= temp_21_0~1664@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                             (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                            )
                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                             (Poly%main!nl_basics.Elem. a~2@)
                                                                                         ))))
                                                                                         (=>
                                                                                          (= temp_21_1~1684@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                              (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                (Poly%main!nl_basics.Elem. a~2@)
                                                                                               )
                                                                                              ) (Poly%main!nl_basics.Elem. d~8@)
                                                                                             )
                                                                                            ) (Poly%main!nl_basics.Elem. a~2@)
                                                                                          ))
                                                                                          (and
                                                                                           (=>
                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                            (=>
                                                                                             %%location_label%%21
                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_21_0~1664@) (Poly%main!nl_basics.Elem.
                                                                                               temp_21_1~1684@
                                                                                           ))))
                                                                                           (=>
                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_21_0~1664@) (Poly%main!nl_basics.Elem.
                                                                                              temp_21_1~1684@
                                                                                            ))
                                                                                            (=>
                                                                                             (= temp_22_0~1731@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                 (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                   (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                )))
                                                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                 (Poly%main!nl_basics.Elem. d~8@)
                                                                                             ))))
                                                                                             (=>
                                                                                              (= temp_22_1~1756@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                  (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                    (Poly%main!nl_basics.Elem. m~10@)
                                                                                                   )
                                                                                                  ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                 )
                                                                                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                  (Poly%main!nl_basics.Elem. d~8@)
                                                                                              ))))
                                                                                              (and
                                                                                               (=>
                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                (=>
                                                                                                 %%location_label%%22
                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_22_0~1731@) (Poly%main!nl_basics.Elem.
                                                                                                   temp_22_1~1756@
                                                                                               ))))
                                                                                               (=>
                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_22_0~1731@) (Poly%main!nl_basics.Elem.
                                                                                                  temp_22_1~1756@
                                                                                                ))
                                                                                                (=>
                                                                                                 (= temp_23_0~1798@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                     (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                    )
                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                     (Poly%main!nl_basics.Elem. d~8@)
                                                                                                 ))))
                                                                                                 (=>
                                                                                                  (= temp_23_1~1818@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                      (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                     )
                                                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                      (Poly%main!nl_basics.Elem. d~8@)
                                                                                                  ))))
                                                                                                  (and
                                                                                                   (=>
                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                    (=>
                                                                                                     %%location_label%%23
                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_23_0~1798@) (Poly%main!nl_basics.Elem.
                                                                                                       temp_23_1~1818@
                                                                                                   ))))
                                                                                                   (=>
                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_23_0~1798@) (Poly%main!nl_basics.Elem.
                                                                                                      temp_23_1~1818@
                                                                                                    ))
                                                                                                    (=>
                                                                                                     (= temp_24_0~1870@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                         (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                           (Poly%main!nl_basics.Elem. b~4@)
                                                                                                          )
                                                                                                         ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                        )
                                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                         (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                           (Poly%main!nl_basics.Elem. m~10@)
                                                                                                     ))))))
                                                                                                     (=>
                                                                                                      (= temp_24_1~1930@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                          (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                              (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                             )
                                                                                                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                  (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                 )
                                                                                                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                  (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                    (Poly%main!nl_basics.Elem. m~10@)
                                                                                                               )))))
                                                                                                              ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                           )))
                                                                                                          ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                         )
                                                                                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                          (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                            (Poly%main!nl_basics.Elem. m~10@)
                                                                                                      ))))))
                                                                                                      (and
                                                                                                       (=>
                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                        (=>
                                                                                                         %%location_label%%24
                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_24_0~1870@) (Poly%main!nl_basics.Elem.
                                                                                                           temp_24_1~1930@
                                                                                                       ))))
                                                                                                       (=>
                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_24_0~1870@) (Poly%main!nl_basics.Elem.
                                                                                                          temp_24_1~1930@
                                                                                                        ))
                                                                                                        (=>
                                                                                                         (= temp_25_0~1982@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                                                             (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                               (Poly%main!nl_basics.Elem. m~10@)
                                                                                                              )
                                                                                                             ) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                            )
                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                               (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                              )
                                                                                                             ) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                         ))))
                                                                                                         (=>
                                                                                                          (= temp_25_1~2012@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                              (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                  (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                 )
                                                                                                                ) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                               )
                                                                                                              ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                (Poly%main!nl_basics.Elem. m~10@)
                                                                                                             )))
                                                                                                            ) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                          ))
                                                                                                          (and
                                                                                                           (=>
                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                            (=>
                                                                                                             %%location_label%%25
                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_25_0~1982@) (Poly%main!nl_basics.Elem.
                                                                                                               temp_25_1~2012@
                                                                                                           ))))
                                                                                                           (=>
                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_25_0~1982@) (Poly%main!nl_basics.Elem.
                                                                                                              temp_25_1~2012@
                                                                                                            ))
                                                                                                            (=>
                                                                                                             (= temp_26_0~2059@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                 (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                )
                                                                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                   (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                  )
                                                                                                                 ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                             ))))
                                                                                                             (=>
                                                                                                              (= temp_26_1~2109@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                  (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                 )
                                                                                                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                    (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                      (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                     )
                                                                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                        (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                          (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                         )
                                                                                                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                          (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                       )))
                                                                                                                      ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                   )))
                                                                                                                  ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                              ))))
                                                                                                              (and
                                                                                                               (=>
                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                (=>
                                                                                                                 %%location_label%%26
                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_26_0~2059@) (Poly%main!nl_basics.Elem.
                                                                                                                   temp_26_1~2109@
                                                                                                               ))))
                                                                                                               (=>
                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_26_0~2059@) (Poly%main!nl_basics.Elem.
                                                                                                                  temp_26_1~2109@
                                                                                                                ))
                                                                                                                (=>
                                                                                                                 (= temp_27_0~2156@ (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                     (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                       (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                      )
                                                                                                                     ) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                    )
                                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                     (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                 ))))
                                                                                                                 (=>
                                                                                                                  (= temp_27_1~2181@ (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                      (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                     )
                                                                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                        (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                       )
                                                                                                                      ) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                  ))))
                                                                                                                  (and
                                                                                                                   (=>
                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                    (=>
                                                                                                                     %%location_label%%27
                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_27_0~2156@) (Poly%main!nl_basics.Elem.
                                                                                                                       temp_27_1~2181@
                                                                                                                   ))))
                                                                                                                   (=>
                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_27_0~2156@) (Poly%main!nl_basics.Elem.
                                                                                                                      temp_27_1~2181@
                                                                                                                    ))
                                                                                                                    (=>
                                                                                                                     (= temp_28_0~2223@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                         (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                        )
                                                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                         (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                     ))))
                                                                                                                     (=>
                                                                                                                      (= temp_28_1~2243@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                          (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                         )
                                                                                                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                          (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                      ))))
                                                                                                                      (and
                                                                                                                       (=>
                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                        (=>
                                                                                                                         %%location_label%%28
                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_28_0~2223@) (Poly%main!nl_basics.Elem.
                                                                                                                           temp_28_1~2243@
                                                                                                                       ))))
                                                                                                                       (=>
                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_28_0~2223@) (Poly%main!nl_basics.Elem.
                                                                                                                          temp_28_1~2243@
                                                                                                                        ))
                                                                                                                        (=>
                                                                                                                         (= temp_29_0~2290@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                             (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                            )
                                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                               (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                              )
                                                                                                                             ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                         ))))
                                                                                                                         (=>
                                                                                                                          (= temp_29_1~2315@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                              (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                             )
                                                                                                                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                               )
                                                                                                                              ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                          ))))
                                                                                                                          (and
                                                                                                                           (=>
                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                            (=>
                                                                                                                             %%location_label%%29
                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_29_0~2290@) (Poly%main!nl_basics.Elem.
                                                                                                                               temp_29_1~2315@
                                                                                                                           ))))
                                                                                                                           (=>
                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_29_0~2290@) (Poly%main!nl_basics.Elem.
                                                                                                                              temp_29_1~2315@
                                                                                                                            ))
                                                                                                                            (=>
                                                                                                                             (= temp_30_0~2372@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                 (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                   (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                  )
                                                                                                                                 ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                     (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                       (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                    )))
                                                                                                                                   ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                )))
                                                                                                                               ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                             ))
                                                                                                                             (=>
                                                                                                                              (= temp_30_1~2407@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                  (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                    (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                   )
                                                                                                                                  ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                      (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                        (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                       )
                                                                                                                                      ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                     )
                                                                                                                                    ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                 )))
                                                                                                                                ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                              ))
                                                                                                                              (and
                                                                                                                               (=>
                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                (=>
                                                                                                                                 %%location_label%%30
                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_30_0~2372@) (Poly%main!nl_basics.Elem.
                                                                                                                                   temp_30_1~2407@
                                                                                                                               ))))
                                                                                                                               (=>
                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_30_0~2372@) (Poly%main!nl_basics.Elem.
                                                                                                                                  temp_30_1~2407@
                                                                                                                                ))
                                                                                                                                (=>
                                                                                                                                 (= temp_31_0~2454@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                                                                                     (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                       (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                      )
                                                                                                                                     ) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                    )
                                                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                     (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                 ))))
                                                                                                                                 (=>
                                                                                                                                  (= temp_31_1~2504@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                                                                                      (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                                                                                          (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                            (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                                                (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                               )
                                                                                                                                              ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                             )))
                                                                                                                                            ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                         )))
                                                                                                                                        ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                       )
                                                                                                                                      ) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                     )
                                                                                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                      (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                  ))))
                                                                                                                                  (and
                                                                                                                                   (=>
                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                    (=>
                                                                                                                                     %%location_label%%31
                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_31_0~2454@) (Poly%main!nl_basics.Elem.
                                                                                                                                       temp_31_1~2504@
                                                                                                                                   ))))
                                                                                                                                   (=>
                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_31_0~2454@) (Poly%main!nl_basics.Elem.
                                                                                                                                      temp_31_1~2504@
                                                                                                                                    ))
                                                                                                                                    (=>
                                                                                                                                     (= temp_32_0~2546@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                         (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                        )
                                                                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                         (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                     ))))
                                                                                                                                     (=>
                                                                                                                                      (= temp_32_1~2566@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem.
                                                                                                                                         (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem.
                                                                                                                                           (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem.
                                                                                                                                             d~8@
                                                                                                                                      )))))))
                                                                                                                                      (and
                                                                                                                                       (=>
                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                        (=>
                                                                                                                                         %%location_label%%32
                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_32_0~2546@) (Poly%main!nl_basics.Elem.
                                                                                                                                           temp_32_1~2566@
                                                                                                                                       ))))
                                                                                                                                       (=>
                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_32_0~2546@) (Poly%main!nl_basics.Elem.
                                                                                                                                          temp_32_1~2566@
                                                                                                                                        ))
                                                                                                                                        (=>
                                                                                                                                         (= temp_33_0~2608@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                             (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                            )
                                                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                             (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                         ))))
                                                                                                                                         (=>
                                                                                                                                          (= temp_33_1~2628@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                              (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                             )
                                                                                                                                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                              (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                          ))))
                                                                                                                                          (and
                                                                                                                                           (=>
                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                            (=>
                                                                                                                                             %%location_label%%33
                                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_33_0~2608@) (Poly%main!nl_basics.Elem.
                                                                                                                                               temp_33_1~2628@
                                                                                                                                           ))))
                                                                                                                                           (=>
                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_33_0~2608@) (Poly%main!nl_basics.Elem.
                                                                                                                                              temp_33_1~2628@
                                                                                                                                            ))
                                                                                                                                            (=>
                                                                                                                                             (= temp_34_0~2670@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                 (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                )
                                                                                                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                 (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                             ))))
                                                                                                                                             (=>
                                                                                                                                              (= temp_34_1~2690@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                  (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                 )
                                                                                                                                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                  (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                              ))))
                                                                                                                                              (and
                                                                                                                                               (=>
                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                (=>
                                                                                                                                                 %%location_label%%34
                                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_34_0~2670@) (Poly%main!nl_basics.Elem.
                                                                                                                                                   temp_34_1~2690@
                                                                                                                                               ))))
                                                                                                                                               (=>
                                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_34_0~2670@) (Poly%main!nl_basics.Elem.
                                                                                                                                                  temp_34_1~2690@
                                                                                                                                                ))
                                                                                                                                                (=>
                                                                                                                                                 (= temp_35_0~2737@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                     (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                       (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                      )
                                                                                                                                                     ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                       (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                    )))
                                                                                                                                                   ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                 ))
                                                                                                                                                 (=>
                                                                                                                                                  (= temp_35_1~2797@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                                                      (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                          (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                         )
                                                                                                                                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                          (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                       )))
                                                                                                                                                      ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                          (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                              (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                             )
                                                                                                                                                            ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                           )
                                                                                                                                                          ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                              (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                             )
                                                                                                                                                            ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                         )))
                                                                                                                                                        ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                     )))
                                                                                                                                                    ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                  ))
                                                                                                                                                  (and
                                                                                                                                                   (=>
                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                    (=>
                                                                                                                                                     %%location_label%%35
                                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_35_0~2737@) (Poly%main!nl_basics.Elem.
                                                                                                                                                       temp_35_1~2797@
                                                                                                                                                   ))))
                                                                                                                                                   (=>
                                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_35_0~2737@) (Poly%main!nl_basics.Elem.
                                                                                                                                                      temp_35_1~2797@
                                                                                                                                                    ))
                                                                                                                                                    (=>
                                                                                                                                                     (= temp_36_0~2844@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                         (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                           (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                          )
                                                                                                                                                         ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                           (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                        )))
                                                                                                                                                       ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                     ))
                                                                                                                                                     (=>
                                                                                                                                                      (= temp_36_1~2869@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                          (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                              (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                             )
                                                                                                                                                            ) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                           )
                                                                                                                                                          ) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                         )
                                                                                                                                                        ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                      ))
                                                                                                                                                      (and
                                                                                                                                                       (=>
                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                        (=>
                                                                                                                                                         %%location_label%%36
                                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_36_0~2844@) (Poly%main!nl_basics.Elem.
                                                                                                                                                           temp_36_1~2869@
                                                                                                                                                       ))))
                                                                                                                                                       (=>
                                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_36_0~2844@) (Poly%main!nl_basics.Elem.
                                                                                                                                                          temp_36_1~2869@
                                                                                                                                                        ))
                                                                                                                                                        (=>
                                                                                                                                                         (= temp_37_0~2911@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                                                                                                             (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                            )
                                                                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                             (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                         ))))
                                                                                                                                                         (=>
                                                                                                                                                          (= temp_37_1~2931@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                                                                                                              (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                             )
                                                                                                                                                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                              (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                          ))))
                                                                                                                                                          (and
                                                                                                                                                           (=>
                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                            (=>
                                                                                                                                                             %%location_label%%37
                                                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_37_0~2911@) (Poly%main!nl_basics.Elem.
                                                                                                                                                               temp_37_1~2931@
                                                                                                                                                           ))))
                                                                                                                                                           (=>
                                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_37_0~2911@) (Poly%main!nl_basics.Elem.
                                                                                                                                                              temp_37_1~2931@
                                                                                                                                                            ))
                                                                                                                                                            (=>
                                                                                                                                                             (= temp_38_0~2973@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                 (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                )
                                                                                                                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                 (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                             ))))
                                                                                                                                                             (=>
                                                                                                                                                              (= temp_38_1~2993@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                  (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                 )
                                                                                                                                                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                  (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                              ))))
                                                                                                                                                              (and
                                                                                                                                                               (=>
                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                (=>
                                                                                                                                                                 %%location_label%%38
                                                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_38_0~2973@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                   temp_38_1~2993@
                                                                                                                                                               ))))
                                                                                                                                                               (=>
                                                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_38_0~2973@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                  temp_38_1~2993@
                                                                                                                                                                ))
                                                                                                                                                                (=>
                                                                                                                                                                 (= temp_39_0~3047@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                     (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                       (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                      )
                                                                                                                                                                     ) (Poly%main!nl_basics.Elem. (main!nl_basics.as_elem.? (I 53)))
                                                                                                                                                                    )
                                                                                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                     (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                 ))))
                                                                                                                                                                 (=>
                                                                                                                                                                  (= temp_39_1~3101@ (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                      (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                          (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                         )
                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.as_elem.? (I 53)))
                                                                                                                                                                       )
                                                                                                                                                                      ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                     )
                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                        (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                          (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                         )
                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.as_elem.? (I 53)))
                                                                                                                                                                       )
                                                                                                                                                                      ) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                  ))))
                                                                                                                                                                  (and
                                                                                                                                                                   (=>
                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                    (=>
                                                                                                                                                                     %%location_label%%39
                                                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_39_0~3047@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                       temp_39_1~3101@
                                                                                                                                                                   ))))
                                                                                                                                                                   (=>
                                                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_39_0~3047@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                      temp_39_1~3101@
                                                                                                                                                                    ))
                                                                                                                                                                    (=>
                                                                                                                                                                     (= temp_40_0~3153@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                         (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                           (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                          )
                                                                                                                                                                         ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                        )
                                                                                                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                           (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                          )
                                                                                                                                                                         ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                     ))))
                                                                                                                                                                     (=>
                                                                                                                                                                      (= temp_40_1~3218@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                          (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                            (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                           )
                                                                                                                                                                          ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                         )
                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                                                                            (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                              (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                             )
                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                    (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                      (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                   )))
                                                                                                                                                                                  ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                 )
                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                  (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                               )))
                                                                                                                                                                              ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                           )))
                                                                                                                                                                          ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                      ))))
                                                                                                                                                                      (and
                                                                                                                                                                       (=>
                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                        (=>
                                                                                                                                                                         %%location_label%%40
                                                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_40_0~3153@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                           temp_40_1~3218@
                                                                                                                                                                       ))))
                                                                                                                                                                       (=>
                                                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_40_0~3153@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                          temp_40_1~3218@
                                                                                                                                                                        ))
                                                                                                                                                                        (=>
                                                                                                                                                                         (= temp_41_0~3260@ (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                                                                                                                             (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                            )
                                                                                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                             (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                         ))))
                                                                                                                                                                         (=>
                                                                                                                                                                          (= temp_41_1~3280@ (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                                                                                                                              (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                             )
                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                              (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                          ))))
                                                                                                                                                                          (and
                                                                                                                                                                           (=>
                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                            (=>
                                                                                                                                                                             %%location_label%%41
                                                                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_41_0~3260@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                               temp_41_1~3280@
                                                                                                                                                                           ))))
                                                                                                                                                                           (=>
                                                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_41_0~3260@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                              temp_41_1~3280@
                                                                                                                                                                            ))
                                                                                                                                                                            (=>
                                                                                                                                                                             (= temp_42_0~3327@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                 (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                   (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                )))
                                                                                                                                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                 (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                             ))))
                                                                                                                                                                             (=>
                                                                                                                                                                              (= temp_42_1~3391@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                  (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                    (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                        (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                            (Poly%main!nl_basics.Elem. (main!nl_basics.as_elem.? (I 6))) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                             d~8@
                                                                                                                                                                                           ))
                                                                                                                                                                                          ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.as_elem.?
                                                                                                                                                                                              (I 69)
                                                                                                                                                                                             )
                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                         )))
                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                       )
                                                                                                                                                                                      ) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                     )
                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                 )))
                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                  (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                              ))))
                                                                                                                                                                              (and
                                                                                                                                                                               (=>
                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                (=>
                                                                                                                                                                                 %%location_label%%42
                                                                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_42_0~3327@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                   temp_42_1~3391@
                                                                                                                                                                               ))))
                                                                                                                                                                               (=>
                                                                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_42_0~3327@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                  temp_42_1~3391@
                                                                                                                                                                                ))
                                                                                                                                                                                (=>
                                                                                                                                                                                 (= temp_43_0~3433@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                                                                                     (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                    )
                                                                                                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                     (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                 ))))
                                                                                                                                                                                 (=>
                                                                                                                                                                                  (= temp_43_1~3463@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                      (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                        (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                     )))
                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                      (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                        (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                  ))))))
                                                                                                                                                                                  (and
                                                                                                                                                                                   (=>
                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                    (=>
                                                                                                                                                                                     %%location_label%%43
                                                                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_43_0~3433@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                       temp_43_1~3463@
                                                                                                                                                                                   ))))
                                                                                                                                                                                   (=>
                                                                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_43_0~3433@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                      temp_43_1~3463@
                                                                                                                                                                                    ))
                                                                                                                                                                                    (=>
                                                                                                                                                                                     (= temp_44_0~3500@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                        (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                          b~4@
                                                                                                                                                                                     )))))
                                                                                                                                                                                     (=>
                                                                                                                                                                                      (= temp_44_1~3515@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                          (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                         )
                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                      ))
                                                                                                                                                                                      (and
                                                                                                                                                                                       (=>
                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                        (=>
                                                                                                                                                                                         %%location_label%%44
                                                                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_44_0~3500@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                           temp_44_1~3515@
                                                                                                                                                                                       ))))
                                                                                                                                                                                       (=>
                                                                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_44_0~3500@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                          temp_44_1~3515@
                                                                                                                                                                                        ))
                                                                                                                                                                                        (=>
                                                                                                                                                                                         (= temp_45_0~3562@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                                                                                                                                             (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                               (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                              )
                                                                                                                                                                                             ) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                            )
                                                                                                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                             (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                         ))))
                                                                                                                                                                                         (=>
                                                                                                                                                                                          (= temp_45_1~3587@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                                                                                                                                              (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                             )))
                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                              (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                          ))))
                                                                                                                                                                                          (and
                                                                                                                                                                                           (=>
                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                            (=>
                                                                                                                                                                                             %%location_label%%45
                                                                                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_45_0~3562@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                               temp_45_1~3587@
                                                                                                                                                                                           ))))
                                                                                                                                                                                           (=>
                                                                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_45_0~3562@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                              temp_45_1~3587@
                                                                                                                                                                                            ))
                                                                                                                                                                                            (=>
                                                                                                                                                                                             (= temp_46_0~3639@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                   (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                  )))
                                                                                                                                                                                                 ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                   (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                )))
                                                                                                                                                                                               ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                             ))
                                                                                                                                                                                             (=>
                                                                                                                                                                                              (= temp_46_1~3669@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                    (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                   )))
                                                                                                                                                                                                  ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                    (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                 )))
                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                              ))
                                                                                                                                                                                              (and
                                                                                                                                                                                               (=>
                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                (=>
                                                                                                                                                                                                 %%location_label%%46
                                                                                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_46_0~3639@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                   temp_46_1~3669@
                                                                                                                                                                                               ))))
                                                                                                                                                                                               (=>
                                                                                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_46_0~3639@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                  temp_46_1~3669@
                                                                                                                                                                                                ))
                                                                                                                                                                                                (=>
                                                                                                                                                                                                 (= temp_47_0~3711@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                    )
                                                                                                                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                 ))))
                                                                                                                                                                                                 (=>
                                                                                                                                                                                                  (= temp_47_1~3731@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                     (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                       (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                         c~6@
                                                                                                                                                                                                  )))))))
                                                                                                                                                                                                  (and
                                                                                                                                                                                                   (=>
                                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                    (=>
                                                                                                                                                                                                     %%location_label%%47
                                                                                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_47_0~3711@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                       temp_47_1~3731@
                                                                                                                                                                                                   ))))
                                                                                                                                                                                                   (=>
                                                                                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_47_0~3711@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                      temp_47_1~3731@
                                                                                                                                                                                                    ))
                                                                                                                                                                                                    (=>
                                                                                                                                                                                                     (= temp_48_0~3780@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                           (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. (main!nl_basics.as_elem.?
                                                                                                                                                                                                             (I 99)
                                                                                                                                                                                                        )))))
                                                                                                                                                                                                       ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                     ))
                                                                                                                                                                                                     (=>
                                                                                                                                                                                                      (= temp_48_1~3837@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                            (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. (main!nl_basics.as_elem.? (I 99)))
                                                                                                                                                                                                           )))
                                                                                                                                                                                                          ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                               )
                                                                                                                                                                                                              ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                 )
                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                             )))
                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                         )))
                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                      ))
                                                                                                                                                                                                      (and
                                                                                                                                                                                                       (=>
                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                        (=>
                                                                                                                                                                                                         %%location_label%%48
                                                                                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_48_0~3780@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                           temp_48_1~3837@
                                                                                                                                                                                                       ))))
                                                                                                                                                                                                       (=>
                                                                                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_48_0~3780@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                          temp_48_1~3837@
                                                                                                                                                                                                        ))
                                                                                                                                                                                                        (=>
                                                                                                                                                                                                         (= temp_49_0~3879@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                            )
                                                                                                                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                         ))))
                                                                                                                                                                                                         (=>
                                                                                                                                                                                                          (= temp_49_1~3899@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                             )
                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                          ))))
                                                                                                                                                                                                          (and
                                                                                                                                                                                                           (=>
                                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                            (=>
                                                                                                                                                                                                             %%location_label%%49
                                                                                                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_49_0~3879@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                               temp_49_1~3899@
                                                                                                                                                                                                           ))))
                                                                                                                                                                                                           (=>
                                                                                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_49_0~3879@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                              temp_49_1~3899@
                                                                                                                                                                                                            ))
                                                                                                                                                                                                            (=>
                                                                                                                                                                                                             (= temp_50_0~3946@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                   (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                  )
                                                                                                                                                                                                                 ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                   (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                )))
                                                                                                                                                                                                               ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                             ))
                                                                                                                                                                                                             (=>
                                                                                                                                                                                                              (= temp_50_1~3981@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                    (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                   )))
                                                                                                                                                                                                                  ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                    (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                 )))))
                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                              ))
                                                                                                                                                                                                              (and
                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                 %%location_label%%50
                                                                                                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_50_0~3946@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                   temp_50_1~3981@
                                                                                                                                                                                                               ))))
                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_50_0~3946@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                  temp_50_1~3981@
                                                                                                                                                                                                                ))
                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                 (= temp_51_0~4028@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                       (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                      )
                                                                                                                                                                                                                     ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                    )
                                                                                                                                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                 ))))
                                                                                                                                                                                                                 (=>
                                                                                                                                                                                                                  (= temp_51_1~4068@ (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                         )
                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                       )
                                                                                                                                                                                                                      ) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                     )
                                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                        (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                         )
                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                       )
                                                                                                                                                                                                                      ) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                  ))))
                                                                                                                                                                                                                  (and
                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                     %%location_label%%51
                                                                                                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_51_0~4028@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                       temp_51_1~4068@
                                                                                                                                                                                                                   ))))
                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_51_0~4028@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                      temp_51_1~4068@
                                                                                                                                                                                                                    ))
                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                     (= temp_52_0~4115@ (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                           (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                          )
                                                                                                                                                                                                                         ) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                        )
                                                                                                                                                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                     ))))
                                                                                                                                                                                                                     (=>
                                                                                                                                                                                                                      (= temp_52_1~4140@ (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                         )
                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                            (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                           )
                                                                                                                                                                                                                          ) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                      ))))
                                                                                                                                                                                                                      (and
                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                         %%location_label%%52
                                                                                                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_52_0~4115@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                           temp_52_1~4140@
                                                                                                                                                                                                                       ))))
                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_52_0~4115@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                          temp_52_1~4140@
                                                                                                                                                                                                                        ))
                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                         (= temp_53_0~4182@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                            )
                                                                                                                                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                         ))))
                                                                                                                                                                                                                         (=>
                                                                                                                                                                                                                          (= temp_53_1~4202@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                             )
                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                          ))))
                                                                                                                                                                                                                          (and
                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                             %%location_label%%53
                                                                                                                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_53_0~4182@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                               temp_53_1~4202@
                                                                                                                                                                                                                           ))))
                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_53_0~4182@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                              temp_53_1~4202@
                                                                                                                                                                                                                            ))
                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                             (= temp_54_0~4249@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                )
                                                                                                                                                                                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                   (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                             ))))))
                                                                                                                                                                                                                             (=>
                                                                                                                                                                                                                              (= temp_54_1~4299@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                 )
                                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                            (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                           )
                                                                                                                                                                                                                                          ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                            (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                         )))
                                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                       )
                                                                                                                                                                                                                                      ) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                     )
                                                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                              ))))))
                                                                                                                                                                                                                              (and
                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                 %%location_label%%54
                                                                                                                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_54_0~4249@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                   temp_54_1~4299@
                                                                                                                                                                                                                               ))))
                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_54_0~4249@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                  temp_54_1~4299@
                                                                                                                                                                                                                                ))
                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                 (= temp_55_0~4346@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                       (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                     ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                       (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                    )))
                                                                                                                                                                                                                                   ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                 ))
                                                                                                                                                                                                                                 (=>
                                                                                                                                                                                                                                  (= temp_55_1~4396@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                         )
                                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                       )))
                                                                                                                                                                                                                                      ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                            (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                           )
                                                                                                                                                                                                                                          ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                            (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                         )))
                                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                     )))
                                                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                  ))
                                                                                                                                                                                                                                  (and
                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                     %%location_label%%55
                                                                                                                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_55_0~4346@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                       temp_55_1~4396@
                                                                                                                                                                                                                                   ))))
                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_55_0~4346@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                      temp_55_1~4396@
                                                                                                                                                                                                                                    ))
                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                     (= temp_56_0~4443@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                           (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                         ) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                     ))))
                                                                                                                                                                                                                                     (=>
                                                                                                                                                                                                                                      (= temp_56_1~4468@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                            (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                           )
                                                                                                                                                                                                                                          ) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                         )
                                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                      ))))
                                                                                                                                                                                                                                      (and
                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                         %%location_label%%56
                                                                                                                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_56_0~4443@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                           temp_56_1~4468@
                                                                                                                                                                                                                                       ))))
                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_56_0~4443@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                          temp_56_1~4468@
                                                                                                                                                                                                                                        ))
                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                         (= temp_57_0~4510@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                         ))))
                                                                                                                                                                                                                                         (=>
                                                                                                                                                                                                                                          (= temp_57_1~4530@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                             )
                                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                          ))))
                                                                                                                                                                                                                                          (and
                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                             %%location_label%%57
                                                                                                                                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_57_0~4510@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                               temp_57_1~4530@
                                                                                                                                                                                                                                           ))))
                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_57_0~4510@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                              temp_57_1~4530@
                                                                                                                                                                                                                                            ))
                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                             (= temp_58_0~4592@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                  )))
                                                                                                                                                                                                                                                 ) (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                   (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                )))))
                                                                                                                                                                                                                                               ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                             ))
                                                                                                                                                                                                                                             (=>
                                                                                                                                                                                                                                              (= temp_58_1~4632@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                     )
                                                                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                   )))
                                                                                                                                                                                                                                                  ) (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                    (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                 )))))
                                                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                              ))
                                                                                                                                                                                                                                              (and
                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                 %%location_label%%58
                                                                                                                                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_58_0~4592@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                   temp_58_1~4632@
                                                                                                                                                                                                                                               ))))
                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_58_0~4592@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                  temp_58_1~4632@
                                                                                                                                                                                                                                                ))
                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                 (= temp_59_0~4679@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                       (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                     ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                 ))))
                                                                                                                                                                                                                                                 (=>
                                                                                                                                                                                                                                                  (= temp_59_1~4704@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                     )
                                                                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                        (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                       )
                                                                                                                                                                                                                                                      ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                  ))))
                                                                                                                                                                                                                                                  (and
                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                     %%location_label%%59
                                                                                                                                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_59_0~4679@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                       temp_59_1~4704@
                                                                                                                                                                                                                                                   ))))
                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_59_0~4679@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                      temp_59_1~4704@
                                                                                                                                                                                                                                                    ))
                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                     (= temp_60_0~4746@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                     ))))
                                                                                                                                                                                                                                                     (=>
                                                                                                                                                                                                                                                      (= temp_60_1~4766@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                         (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                           (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                             d~8@
                                                                                                                                                                                                                                                      )))))))
                                                                                                                                                                                                                                                      (and
                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                         %%location_label%%60
                                                                                                                                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_60_0~4746@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                           temp_60_1~4766@
                                                                                                                                                                                                                                                       ))))
                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_60_0~4746@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                          temp_60_1~4766@
                                                                                                                                                                                                                                                        ))
                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                         (= temp_61_0~4813@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                               (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                             ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                         ))))
                                                                                                                                                                                                                                                         (=>
                                                                                                                                                                                                                                                          (= temp_61_1~4838@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                             (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                               (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                   c~6@
                                                                                                                                                                                                                                                                  ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                 )
                                                                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                          ))))))
                                                                                                                                                                                                                                                          (and
                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                             %%location_label%%61
                                                                                                                                                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_61_0~4813@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                               temp_61_1~4838@
                                                                                                                                                                                                                                                           ))))
                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_61_0~4813@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                              temp_61_1~4838@
                                                                                                                                                                                                                                                            ))
                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                             (= temp_62_0~4890@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                   (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                 ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                   ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                )))
                                                                                                                                                                                                                                                               ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                             ))
                                                                                                                                                                                                                                                             (=>
                                                                                                                                                                                                                                                              (= temp_62_1~4920@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                     )
                                                                                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                   )))
                                                                                                                                                                                                                                                                  ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                 )
                                                                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                              ))
                                                                                                                                                                                                                                                              (and
                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                 %%location_label%%62
                                                                                                                                                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_62_0~4890@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                   temp_62_1~4920@
                                                                                                                                                                                                                                                               ))))
                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_62_0~4890@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                  temp_62_1~4920@
                                                                                                                                                                                                                                                                ))
                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                 (= temp_63_0~4972@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                                       ) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                     ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                 ))))
                                                                                                                                                                                                                                                                 (=>
                                                                                                                                                                                                                                                                  (= temp_63_1~5032@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                            (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                    (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                   )
                                                                                                                                                                                                                                                                                  ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                 )
                                                                                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                               )))
                                                                                                                                                                                                                                                                              ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                           )))
                                                                                                                                                                                                                                                                          ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                         )
                                                                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                       )
                                                                                                                                                                                                                                                                      ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                     )
                                                                                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                  ))))
                                                                                                                                                                                                                                                                  (and
                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                     %%location_label%%63
                                                                                                                                                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_63_0~4972@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                       temp_63_1~5032@
                                                                                                                                                                                                                                                                   ))))
                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_63_0~4972@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                      temp_63_1~5032@
                                                                                                                                                                                                                                                                    ))
                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                     (= temp_64_0~5074@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                     ))))
                                                                                                                                                                                                                                                                     (=>
                                                                                                                                                                                                                                                                      (= temp_64_1~5094@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                         )
                                                                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                      ))))
                                                                                                                                                                                                                                                                      (and
                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                         %%location_label%%64
                                                                                                                                                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_64_0~5074@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                           temp_64_1~5094@
                                                                                                                                                                                                                                                                       ))))
                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_64_0~5074@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                          temp_64_1~5094@
                                                                                                                                                                                                                                                                        ))
                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                         (= temp_65_0~5136@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                         ))))
                                                                                                                                                                                                                                                                         (=>
                                                                                                                                                                                                                                                                          (= temp_65_1~5156@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                               )
                                                                                                                                                                                                                                                                              ) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                             )
                                                                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                          ))
                                                                                                                                                                                                                                                                          (and
                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                             %%location_label%%65
                                                                                                                                                                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_65_0~5136@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                               temp_65_1~5156@
                                                                                                                                                                                                                                                                           ))))
                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_65_0~5136@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                              temp_65_1~5156@
                                                                                                                                                                                                                                                                            ))
                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                             (= temp_66_0~5203@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                   (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                                 ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                             ))))
                                                                                                                                                                                                                                                                             (=>
                                                                                                                                                                                                                                                                              (= temp_66_1~5228@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                 )
                                                                                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                    (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                   )
                                                                                                                                                                                                                                                                                  ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                              ))))
                                                                                                                                                                                                                                                                              (and
                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                 %%location_label%%66
                                                                                                                                                                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_66_0~5203@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                   temp_66_1~5228@
                                                                                                                                                                                                                                                                               ))))
                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_66_0~5203@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                  temp_66_1~5228@
                                                                                                                                                                                                                                                                                ))
                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                 (= temp_67_0~5270@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                 ))))
                                                                                                                                                                                                                                                                                 (=>
                                                                                                                                                                                                                                                                                  (= temp_67_1~5290@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                     )
                                                                                                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                  ))))
                                                                                                                                                                                                                                                                                  (and
                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                     %%location_label%%67
                                                                                                                                                                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_67_0~5270@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                       temp_67_1~5290@
                                                                                                                                                                                                                                                                                   ))))
                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_67_0~5270@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                      temp_67_1~5290@
                                                                                                                                                                                                                                                                                    ))
                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                     (= temp_68_0~5337@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                           (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                                         ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                     ))))
                                                                                                                                                                                                                                                                                     (=>
                                                                                                                                                                                                                                                                                      (= temp_68_1~5397@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                    (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                        (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                     )))
                                                                                                                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                   )))
                                                                                                                                                                                                                                                                                                  ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                 )
                                                                                                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                             )))
                                                                                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                           )
                                                                                                                                                                                                                                                                                          ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                         )
                                                                                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                      ))))
                                                                                                                                                                                                                                                                                      (and
                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                         %%location_label%%68
                                                                                                                                                                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_68_0~5337@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                           temp_68_1~5397@
                                                                                                                                                                                                                                                                                       ))))
                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_68_0~5337@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                          temp_68_1~5397@
                                                                                                                                                                                                                                                                                        ))
                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                         (= temp_69_0~5449@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                               (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                            )))
                                                                                                                                                                                                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                               (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                         ))))))
                                                                                                                                                                                                                                                                                         (=>
                                                                                                                                                                                                                                                                                          (= temp_69_1~5479@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                             (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                 c~6@
                                                                                                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                               )
                                                                                                                                                                                                                                                                                              ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                          ))))))))
                                                                                                                                                                                                                                                                                          (and
                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                             %%location_label%%69
                                                                                                                                                                                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_69_0~5449@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                               temp_69_1~5479@
                                                                                                                                                                                                                                                                                           ))))
                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_69_0~5449@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                              temp_69_1~5479@
                                                                                                                                                                                                                                                                                            ))
                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                             (= temp_70_0~5521@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                             ))))
                                                                                                                                                                                                                                                                                             (=>
                                                                                                                                                                                                                                                                                              (= temp_70_1~5541@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                 )
                                                                                                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                              ))))
                                                                                                                                                                                                                                                                                              (and
                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                 %%location_label%%70
                                                                                                                                                                                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_70_0~5521@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                   temp_70_1~5541@
                                                                                                                                                                                                                                                                                               ))))
                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_70_0~5521@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                  temp_70_1~5541@
                                                                                                                                                                                                                                                                                                ))
                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                 (= temp_71_0~5583@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                 ))))
                                                                                                                                                                                                                                                                                                 (=>
                                                                                                                                                                                                                                                                                                  (= temp_71_1~5603@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                     (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                       (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                         c~6@
                                                                                                                                                                                                                                                                                                  )))))))
                                                                                                                                                                                                                                                                                                  (and
                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                     %%location_label%%71
                                                                                                                                                                                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_71_0~5583@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                       temp_71_1~5603@
                                                                                                                                                                                                                                                                                                   ))))
                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_71_0~5583@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                      temp_71_1~5603@
                                                                                                                                                                                                                                                                                                    ))
                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                     (= temp_72_0~5645@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                     ))))
                                                                                                                                                                                                                                                                                                     (=>
                                                                                                                                                                                                                                                                                                      (= temp_72_1~5665@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                         (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                           (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                             c~6@
                                                                                                                                                                                                                                                                                                      )))))))
                                                                                                                                                                                                                                                                                                      (and
                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                         %%location_label%%72
                                                                                                                                                                                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_72_0~5645@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                           temp_72_1~5665@
                                                                                                                                                                                                                                                                                                       ))))
                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_72_0~5645@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                          temp_72_1~5665@
                                                                                                                                                                                                                                                                                                        ))
                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                         (= temp_73_0~5712@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                               (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                                                                             ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                         ))))
                                                                                                                                                                                                                                                                                                         (=>
                                                                                                                                                                                                                                                                                                          (= temp_73_1~5737@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                 )
                                                                                                                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                               )
                                                                                                                                                                                                                                                                                                              ) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                             )
                                                                                                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                          ))
                                                                                                                                                                                                                                                                                                          (and
                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                             %%location_label%%73
                                                                                                                                                                                                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_73_0~5712@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                               temp_73_1~5737@
                                                                                                                                                                                                                                                                                                           ))))
                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_73_0~5712@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                              temp_73_1~5737@
                                                                                                                                                                                                                                                                                                            ))
                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                             (= temp_74_0~5779@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                             ))))
                                                                                                                                                                                                                                                                                                             (=>
                                                                                                                                                                                                                                                                                                              (= temp_74_1~5799@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                    (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                   )
                                                                                                                                                                                                                                                                                                                  ) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                 )
                                                                                                                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                              ))
                                                                                                                                                                                                                                                                                                              (and
                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                 %%location_label%%74
                                                                                                                                                                                                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_74_0~5779@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                   temp_74_1~5799@
                                                                                                                                                                                                                                                                                                               ))))
                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_74_0~5779@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                  temp_74_1~5799@
                                                                                                                                                                                                                                                                                                                ))
                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                 (= temp_75_0~5851@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                       (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                                                                     ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                       (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                                                                     ) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                 ))))
                                                                                                                                                                                                                                                                                                                 (=>
                                                                                                                                                                                                                                                                                                                  (= temp_75_1~5881@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                        (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                       )
                                                                                                                                                                                                                                                                                                                      ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                     )
                                                                                                                                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                        (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                  ))))))
                                                                                                                                                                                                                                                                                                                  (and
                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                     %%location_label%%75
                                                                                                                                                                                                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_75_0~5851@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                       temp_75_1~5881@
                                                                                                                                                                                                                                                                                                                   ))))
                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_75_0~5851@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                      temp_75_1~5881@
                                                                                                                                                                                                                                                                                                                    ))
                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                     (= temp_76_0~5933@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                                                                                                           ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                                                                         ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                           (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                        )))
                                                                                                                                                                                                                                                                                                                       ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                     ))
                                                                                                                                                                                                                                                                                                                     (=>
                                                                                                                                                                                                                                                                                                                      (= temp_76_1~5963@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                               )
                                                                                                                                                                                                                                                                                                                              ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                             )
                                                                                                                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                           )
                                                                                                                                                                                                                                                                                                                          ) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                         )
                                                                                                                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                      ))
                                                                                                                                                                                                                                                                                                                      (and
                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                         %%location_label%%76
                                                                                                                                                                                                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_76_0~5933@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                           temp_76_1~5963@
                                                                                                                                                                                                                                                                                                                       ))))
                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_76_0~5933@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                          temp_76_1~5963@
                                                                                                                                                                                                                                                                                                                        ))
                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                         (= temp_77_0~6010@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                               (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                            )))
                                                                                                                                                                                                                                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                         ))))
                                                                                                                                                                                                                                                                                                                         (=>
                                                                                                                                                                                                                                                                                                                          (= temp_77_1~6060@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                        (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                       )
                                                                                                                                                                                                                                                                                                                                      ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                        (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                     )))
                                                                                                                                                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                 )))
                                                                                                                                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                             )))
                                                                                                                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                          ))))
                                                                                                                                                                                                                                                                                                                          (and
                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                                             %%location_label%%77
                                                                                                                                                                                                                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_77_0~6010@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                               temp_77_1~6060@
                                                                                                                                                                                                                                                                                                                           ))))
                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_77_0~6010@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                              temp_77_1~6060@
                                                                                                                                                                                                                                                                                                                            ))
                                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                                             (= temp_78_0~6102@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                                                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                             ))))
                                                                                                                                                                                                                                                                                                                             (=>
                                                                                                                                                                                                                                                                                                                              (= temp_78_1~6122@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                 (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                   (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                     b~4@
                                                                                                                                                                                                                                                                                                                              )))))))
                                                                                                                                                                                                                                                                                                                              (and
                                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                                 %%location_label%%78
                                                                                                                                                                                                                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_78_0~6102@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                   temp_78_1~6122@
                                                                                                                                                                                                                                                                                                                               ))))
                                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_78_0~6102@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                  temp_78_1~6122@
                                                                                                                                                                                                                                                                                                                                ))
                                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                                 (= temp_79_0~6174@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                       (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                                                                                     ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                       (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                 ))))))
                                                                                                                                                                                                                                                                                                                                 (=>
                                                                                                                                                                                                                                                                                                                                  (= temp_79_1~6234@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                         )
                                                                                                                                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                            (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                             )
                                                                                                                                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                               )
                                                                                                                                                                                                                                                                                                                                              ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                           )))
                                                                                                                                                                                                                                                                                                                                          ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                       )))
                                                                                                                                                                                                                                                                                                                                      ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                     )
                                                                                                                                                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                        (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                  ))))))
                                                                                                                                                                                                                                                                                                                                  (and
                                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                                     %%location_label%%79
                                                                                                                                                                                                                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_79_0~6174@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                       temp_79_1~6234@
                                                                                                                                                                                                                                                                                                                                   ))))
                                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_79_0~6174@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                      temp_79_1~6234@
                                                                                                                                                                                                                                                                                                                                    ))
                                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                                     (= temp_80_0~6276@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                     ))))
                                                                                                                                                                                                                                                                                                                                     (=>
                                                                                                                                                                                                                                                                                                                                      (= temp_80_1~6296@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                         )
                                                                                                                                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                      ))))
                                                                                                                                                                                                                                                                                                                                      (and
                                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                                         %%location_label%%80
                                                                                                                                                                                                                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_80_0~6276@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                           temp_80_1~6296@
                                                                                                                                                                                                                                                                                                                                       ))))
                                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_80_0~6276@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                          temp_80_1~6296@
                                                                                                                                                                                                                                                                                                                                        ))
                                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                                         (= temp_81_0~6348@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                               (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                            )))
                                                                                                                                                                                                                                                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                               (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                         ))))))
                                                                                                                                                                                                                                                                                                                                         (=>
                                                                                                                                                                                                                                                                                                                                          (= temp_81_1~6408@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                        (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                       )))
                                                                                                                                                                                                                                                                                                                                                      ) (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                        (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                     )))
                                                                                                                                                                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                 )))
                                                                                                                                                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                             )))
                                                                                                                                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                          ))))))
                                                                                                                                                                                                                                                                                                                                          (and
                                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                                                             %%location_label%%81
                                                                                                                                                                                                                                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_81_0~6348@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                               temp_81_1~6408@
                                                                                                                                                                                                                                                                                                                                           ))))
                                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_81_0~6348@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                              temp_81_1~6408@
                                                                                                                                                                                                                                                                                                                                            ))
                                                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                                                             (= temp_82_0~6455@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                   (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                )))
                                                                                                                                                                                                                                                                                                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                             ))))
                                                                                                                                                                                                                                                                                                                                             (=>
                                                                                                                                                                                                                                                                                                                                              (= temp_82_1~6510@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                    (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                            (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                           )
                                                                                                                                                                                                                                                                                                                                                          ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                             )
                                                                                                                                                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                         )))
                                                                                                                                                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                     )))
                                                                                                                                                                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                 )))
                                                                                                                                                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                              ))))
                                                                                                                                                                                                                                                                                                                                              (and
                                                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                                                 %%location_label%%82
                                                                                                                                                                                                                                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_82_0~6455@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                   temp_82_1~6510@
                                                                                                                                                                                                                                                                                                                                               ))))
                                                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_82_0~6455@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                  temp_82_1~6510@
                                                                                                                                                                                                                                                                                                                                                ))
                                                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                                                 (= temp_83_0~6552@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                       (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                    )))
                                                                                                                                                                                                                                                                                                                                                   ) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                 ))
                                                                                                                                                                                                                                                                                                                                                 (=>
                                                                                                                                                                                                                                                                                                                                                  (= temp_83_1~6572@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                        (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                       )
                                                                                                                                                                                                                                                                                                                                                      ) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                     )
                                                                                                                                                                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                  ))
                                                                                                                                                                                                                                                                                                                                                  (and
                                                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                                                     %%location_label%%83
                                                                                                                                                                                                                                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_83_0~6552@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                       temp_83_1~6572@
                                                                                                                                                                                                                                                                                                                                                   ))))
                                                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_83_0~6552@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                      temp_83_1~6572@
                                                                                                                                                                                                                                                                                                                                                    ))
                                                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                                                     (= temp_84_0~6624@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                                                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                           (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                                                                                                         ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                           (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                     ))))))
                                                                                                                                                                                                                                                                                                                                                     (=>
                                                                                                                                                                                                                                                                                                                                                      (= temp_84_1~6684@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                         )
                                                                                                                                                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                            (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                     )
                                                                                                                                                                                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                   )))
                                                                                                                                                                                                                                                                                                                                                                  ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                 )
                                                                                                                                                                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                             )))
                                                                                                                                                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                           )
                                                                                                                                                                                                                                                                                                                                                          ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                            (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                      ))))))
                                                                                                                                                                                                                                                                                                                                                      (and
                                                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                                                         %%location_label%%84
                                                                                                                                                                                                                                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_84_0~6624@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                           temp_84_1~6684@
                                                                                                                                                                                                                                                                                                                                                       ))))
                                                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_84_0~6624@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                          temp_84_1~6684@
                                                                                                                                                                                                                                                                                                                                                        ))
                                                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                                                         (= temp_85_0~6736@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                               (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                                                                                                                             ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                                                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                               (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                                                                                                                             ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                         ))))
                                                                                                                                                                                                                                                                                                                                                         (=>
                                                                                                                                                                                                                                                                                                                                                          (= temp_85_1~6766@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                               )
                                                                                                                                                                                                                                                                                                                                                              ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                             )
                                                                                                                                                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                               )
                                                                                                                                                                                                                                                                                                                                                              ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                          ))))
                                                                                                                                                                                                                                                                                                                                                          (and
                                                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                                                                             %%location_label%%85
                                                                                                                                                                                                                                                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_85_0~6736@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                               temp_85_1~6766@
                                                                                                                                                                                                                                                                                                                                                           ))))
                                                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_85_0~6736@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                              temp_85_1~6766@
                                                                                                                                                                                                                                                                                                                                                            ))
                                                                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                                                                             (= temp_86_0~6813@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                   (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                                                                                                                 ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                                                                                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                             ))))
                                                                                                                                                                                                                                                                                                                                                             (=>
                                                                                                                                                                                                                                                                                                                                                              (= temp_86_1~6838@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                    (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                   )
                                                                                                                                                                                                                                                                                                                                                                  ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                 )
                                                                                                                                                                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                              ))))
                                                                                                                                                                                                                                                                                                                                                              (and
                                                                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                                                                 %%location_label%%86
                                                                                                                                                                                                                                                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_86_0~6813@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                   temp_86_1~6838@
                                                                                                                                                                                                                                                                                                                                                               ))))
                                                                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_86_0~6813@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                  temp_86_1~6838@
                                                                                                                                                                                                                                                                                                                                                                ))
                                                                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                                                                 (= temp_87_0~6890@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                       (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                                                                                                                     ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                                       (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                                                                                                                     ) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                 ))))
                                                                                                                                                                                                                                                                                                                                                                 (=>
                                                                                                                                                                                                                                                                                                                                                                  (= temp_87_1~6955@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                        (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                       )
                                                                                                                                                                                                                                                                                                                                                                      ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                     )
                                                                                                                                                                                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                                        (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                 )
                                                                                                                                                                                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                               )))
                                                                                                                                                                                                                                                                                                                                                                              ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                             )))
                                                                                                                                                                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                         )))
                                                                                                                                                                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                       )
                                                                                                                                                                                                                                                                                                                                                                      ) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                  ))))
                                                                                                                                                                                                                                                                                                                                                                  (and
                                                                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                                                                     %%location_label%%87
                                                                                                                                                                                                                                                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_87_0~6890@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                       temp_87_1~6955@
                                                                                                                                                                                                                                                                                                                                                                   ))))
                                                                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_87_0~6890@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                      temp_87_1~6955@
                                                                                                                                                                                                                                                                                                                                                                    ))
                                                                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                                                                     (= temp_88_0~7004@ (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                                                                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.as_elem.?
                                                                                                                                                                                                                                                                                                                                                                           (I 60)
                                                                                                                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                                                                                                                         ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                     ))))
                                                                                                                                                                                                                                                                                                                                                                     (=>
                                                                                                                                                                                                                                                                                                                                                                      (= temp_88_1~7031@ (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. (main!nl_basics.as_elem.? (I 60))) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                           c~6@
                                                                                                                                                                                                                                                                                                                                                                         ))
                                                                                                                                                                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                      ))))
                                                                                                                                                                                                                                                                                                                                                                      (and
                                                                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                                                                         %%location_label%%88
                                                                                                                                                                                                                                                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_88_0~7004@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                           temp_88_1~7031@
                                                                                                                                                                                                                                                                                                                                                                       ))))
                                                                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_88_0~7004@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                          temp_88_1~7031@
                                                                                                                                                                                                                                                                                                                                                                        ))
                                                                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                                                                         (= temp_89_0~7073@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                                                                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                         ))))
                                                                                                                                                                                                                                                                                                                                                                         (=>
                                                                                                                                                                                                                                                                                                                                                                          (= temp_89_1~7093@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                               )
                                                                                                                                                                                                                                                                                                                                                                              ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                             )
                                                                                                                                                                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                          ))
                                                                                                                                                                                                                                                                                                                                                                          (and
                                                                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                                                                                             %%location_label%%89
                                                                                                                                                                                                                                                                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_89_0~7073@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                               temp_89_1~7093@
                                                                                                                                                                                                                                                                                                                                                                           ))))
                                                                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_89_0~7073@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                              temp_89_1~7093@
                                                                                                                                                                                                                                                                                                                                                                            ))
                                                                                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                                                                                             (= temp_90_0~7145@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                   (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                                                                                                                                 ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                                                                                                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                                                   (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                                                                                                                                 ) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                             ))))
                                                                                                                                                                                                                                                                                                                                                                             (=>
                                                                                                                                                                                                                                                                                                                                                                              (= temp_90_1~7200@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                    (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                   )
                                                                                                                                                                                                                                                                                                                                                                                  ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                 )
                                                                                                                                                                                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                                                    (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                            (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                           )
                                                                                                                                                                                                                                                                                                                                                                                          ) (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                            (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                         )))
                                                                                                                                                                                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                     )))
                                                                                                                                                                                                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                   )
                                                                                                                                                                                                                                                                                                                                                                                  ) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                              ))))
                                                                                                                                                                                                                                                                                                                                                                              (and
                                                                                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                                                                                 %%location_label%%90
                                                                                                                                                                                                                                                                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_90_0~7145@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                   temp_90_1~7200@
                                                                                                                                                                                                                                                                                                                                                                               ))))
                                                                                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_90_0~7145@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                  temp_90_1~7200@
                                                                                                                                                                                                                                                                                                                                                                                ))
                                                                                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                                                                                 (= temp_91_0~7249@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                                                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. (main!nl_basics.as_elem.? (I 52)))
                                                                                                                                                                                                                                                                                                                                                                                 ))))
                                                                                                                                                                                                                                                                                                                                                                                 (=>
                                                                                                                                                                                                                                                                                                                                                                                  (= temp_91_1~7276@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. (main!nl_basics.as_elem.?
                                                                                                                                                                                                                                                                                                                                                                                        (I 52)
                                                                                                                                                                                                                                                                                                                                                                                     )))
                                                                                                                                                                                                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                  ))))
                                                                                                                                                                                                                                                                                                                                                                                  (and
                                                                                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                                                                                     %%location_label%%91
                                                                                                                                                                                                                                                                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_91_0~7249@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                       temp_91_1~7276@
                                                                                                                                                                                                                                                                                                                                                                                   ))))
                                                                                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_91_0~7249@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                      temp_91_1~7276@
                                                                                                                                                                                                                                                                                                                                                                                    ))
                                                                                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                                                                                     (= temp_92_0~7318@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                                                                                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                     ))))
                                                                                                                                                                                                                                                                                                                                                                                     (=>
                                                                                                                                                                                                                                                                                                                                                                                      (= temp_92_1~7338@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                         )
                                                                                                                                                                                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                      ))))
                                                                                                                                                                                                                                                                                                                                                                                      (and
                                                                                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                                                                                         %%location_label%%92
                                                                                                                                                                                                                                                                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_92_0~7318@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                           temp_92_1~7338@
                                                                                                                                                                                                                                                                                                                                                                                       ))))
                                                                                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_92_0~7318@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                          temp_92_1~7338@
                                                                                                                                                                                                                                                                                                                                                                                        ))
                                                                                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                                                                                         (= temp_93_0~7380@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                                                                                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                         ))))
                                                                                                                                                                                                                                                                                                                                                                                         (=>
                                                                                                                                                                                                                                                                                                                                                                                          (= temp_93_1~7400@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                             )
                                                                                                                                                                                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                          ))))
                                                                                                                                                                                                                                                                                                                                                                                          (and
                                                                                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                                                                                                             %%location_label%%93
                                                                                                                                                                                                                                                                                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_93_0~7380@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                               temp_93_1~7400@
                                                                                                                                                                                                                                                                                                                                                                                           ))))
                                                                                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_93_0~7380@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                              temp_93_1~7400@
                                                                                                                                                                                                                                                                                                                                                                                            ))
                                                                                                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                                                                                                             (= temp_94_0~7444@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.as_elem.? (I 13)))
                                                                                                                                                                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                             ))))
                                                                                                                                                                                                                                                                                                                                                                                             (=>
                                                                                                                                                                                                                                                                                                                                                                                              (= temp_94_1~7466@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                 (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                   (main!nl_basics.as_elem.? (I 13))
                                                                                                                                                                                                                                                                                                                                                                                              )))))
                                                                                                                                                                                                                                                                                                                                                                                              (and
                                                                                                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                                                                                                 %%location_label%%94
                                                                                                                                                                                                                                                                                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_94_0~7444@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                   temp_94_1~7466@
                                                                                                                                                                                                                                                                                                                                                                                               ))))
                                                                                                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_94_0~7444@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                  temp_94_1~7466@
                                                                                                                                                                                                                                                                                                                                                                                                ))
                                                                                                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                                                                                                 (= temp_95_0~7513@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                                       (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                                                                                                                                                     ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                                                                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                 ))))
                                                                                                                                                                                                                                                                                                                                                                                                 (=>
                                                                                                                                                                                                                                                                                                                                                                                                  (= temp_95_1~7553@ (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                         )
                                                                                                                                                                                                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                       )
                                                                                                                                                                                                                                                                                                                                                                                                      ) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                                     )
                                                                                                                                                                                                                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                        (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                         )
                                                                                                                                                                                                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                       )
                                                                                                                                                                                                                                                                                                                                                                                                      ) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                  ))))
                                                                                                                                                                                                                                                                                                                                                                                                  (and
                                                                                                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                                                                                                     %%location_label%%95
                                                                                                                                                                                                                                                                                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_95_0~7513@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                       temp_95_1~7553@
                                                                                                                                                                                                                                                                                                                                                                                                   ))))
                                                                                                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_95_0~7513@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                      temp_95_1~7553@
                                                                                                                                                                                                                                                                                                                                                                                                    ))
                                                                                                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                                                                                                     (= temp_96_0~7595@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                                                                                                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                     ))))
                                                                                                                                                                                                                                                                                                                                                                                                     (=>
                                                                                                                                                                                                                                                                                                                                                                                                      (= temp_96_1~7615@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                         (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                           (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                             d~8@
                                                                                                                                                                                                                                                                                                                                                                                                      )))))))
                                                                                                                                                                                                                                                                                                                                                                                                      (and
                                                                                                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                                                                                                         %%location_label%%96
                                                                                                                                                                                                                                                                                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_96_0~7595@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                           temp_96_1~7615@
                                                                                                                                                                                                                                                                                                                                                                                                       ))))
                                                                                                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_96_0~7595@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                          temp_96_1~7615@
                                                                                                                                                                                                                                                                                                                                                                                                        ))
                                                                                                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                                                                                                         (= temp_97_0~7667@ (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                                                                               (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                            )))
                                                                                                                                                                                                                                                                                                                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                               (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                                                                                                                                                                             ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                         ))))
                                                                                                                                                                                                                                                                                                                                                                                                         (=>
                                                                                                                                                                                                                                                                                                                                                                                                          (= temp_97_1~7697@ (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                                                                                (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                             )))
                                                                                                                                                                                                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                                (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                               )
                                                                                                                                                                                                                                                                                                                                                                                                              ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                          ))))
                                                                                                                                                                                                                                                                                                                                                                                                          (and
                                                                                                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                                                                                                                             %%location_label%%97
                                                                                                                                                                                                                                                                                                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_97_0~7667@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                               temp_97_1~7697@
                                                                                                                                                                                                                                                                                                                                                                                                           ))))
                                                                                                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_97_0~7667@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                              temp_97_1~7697@
                                                                                                                                                                                                                                                                                                                                                                                                            ))
                                                                                                                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                                                                                                                             (= temp_98_0~7751@ (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                                                                                                                                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                                                                                   (Poly%main!nl_basics.Elem. (main!nl_basics.as_elem.? (I 43))) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                    m~10@
                                                                                                                                                                                                                                                                                                                                                                                                                  ))
                                                                                                                                                                                                                                                                                                                                                                                                                 ) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                             ))))
                                                                                                                                                                                                                                                                                                                                                                                                             (=>
                                                                                                                                                                                                                                                                                                                                                                                                              (= temp_98_1~7783@ (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                                 )
                                                                                                                                                                                                                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                                                                                    (Poly%main!nl_basics.Elem. (main!nl_basics.as_elem.? (I 43))) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                     m~10@
                                                                                                                                                                                                                                                                                                                                                                                                                   ))
                                                                                                                                                                                                                                                                                                                                                                                                                  ) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                              ))))
                                                                                                                                                                                                                                                                                                                                                                                                              (and
                                                                                                                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                                                                                                                 %%location_label%%98
                                                                                                                                                                                                                                                                                                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_98_0~7751@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                   temp_98_1~7783@
                                                                                                                                                                                                                                                                                                                                                                                                               ))))
                                                                                                                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_98_0~7751@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                  temp_98_1~7783@
                                                                                                                                                                                                                                                                                                                                                                                                                ))
                                                                                                                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                                                                                                                 (= temp_99_0~7825@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                                                                                                                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                                                                                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                                                 ))))
                                                                                                                                                                                                                                                                                                                                                                                                                 (=>
                                                                                                                                                                                                                                                                                                                                                                                                                  (= temp_99_1~7845@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                                                     )
                                                                                                                                                                                                                                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                                  ))))
                                                                                                                                                                                                                                                                                                                                                                                                                  (and
                                                                                                                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                                                                                                                     %%location_label%%99
                                                                                                                                                                                                                                                                                                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_99_0~7825@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                       temp_99_1~7845@
                                                                                                                                                                                                                                                                                                                                                                                                                   ))))
                                                                                                                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_99_0~7825@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                      temp_99_1~7845@
                                                                                                                                                                                                                                                                                                                                                                                                                    ))
                                                                                                                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                                                                                                                     (= temp_100_0~7887@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                                                                                                                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                                     ))))
                                                                                                                                                                                                                                                                                                                                                                                                                     (=>
                                                                                                                                                                                                                                                                                                                                                                                                                      (= temp_100_1~7907@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                                         )
                                                                                                                                                                                                                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                                      ))))
                                                                                                                                                                                                                                                                                                                                                                                                                      (and
                                                                                                                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                                                                                                                         %%location_label%%100
                                                                                                                                                                                                                                                                                                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_100_0~7887@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                           temp_100_1~7907@
                                                                                                                                                                                                                                                                                                                                                                                                                       ))))
                                                                                                                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_100_0~7887@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                          temp_100_1~7907@
                                                                                                                                                                                                                                                                                                                                                                                                                        ))
                                                                                                                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                                                                                                                         (= temp_101_0~7954@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                                                                                                                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                                                                                               (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                                                                                                                                                                                             ) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                                                         ))))
                                                                                                                                                                                                                                                                                                                                                                                                                         (=>
                                                                                                                                                                                                                                                                                                                                                                                                                          (= temp_101_1~7979@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                                             )
                                                                                                                                                                                                                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                                                                                                (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                                               )
                                                                                                                                                                                                                                                                                                                                                                                                                              ) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                                                          ))))
                                                                                                                                                                                                                                                                                                                                                                                                                          (and
                                                                                                                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                                                                                                                                             %%location_label%%101
                                                                                                                                                                                                                                                                                                                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_101_0~7954@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                               temp_101_1~7979@
                                                                                                                                                                                                                                                                                                                                                                                                                           ))))
                                                                                                                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_101_0~7954@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                              temp_101_1~7979@
                                                                                                                                                                                                                                                                                                                                                                                                                            ))
                                                                                                                                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                                                                                                                                             (= temp_102_0~8028@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                                                                                                                                                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.as_elem.?
                                                                                                                                                                                                                                                                                                                                                                                                                                   (I 41)
                                                                                                                                                                                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                                                                                                                                                                                 ) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                                             ))))
                                                                                                                                                                                                                                                                                                                                                                                                                             (=>
                                                                                                                                                                                                                                                                                                                                                                                                                              (= temp_102_1~8055@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                                 (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                                   (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.as_elem.? (I 41)))
                                                                                                                                                                                                                                                                                                                                                                                                                                    (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                                              ))))))
                                                                                                                                                                                                                                                                                                                                                                                                                              (and
                                                                                                                                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                 %%location_label%%102
                                                                                                                                                                                                                                                                                                                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_102_0~8028@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                                   temp_102_1~8055@
                                                                                                                                                                                                                                                                                                                                                                                                                               ))))
                                                                                                                                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_102_0~8028@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                                  temp_102_1~8055@
                                                                                                                                                                                                                                                                                                                                                                                                                                ))
                                                                                                                                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                 (= temp_103_0~8102@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                                                                                                       (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                                                    )))
                                                                                                                                                                                                                                                                                                                                                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                                                 ))))
                                                                                                                                                                                                                                                                                                                                                                                                                                 (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                  (= temp_103_1~8127@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                                                        (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                                                       )))
                                                                                                                                                                                                                                                                                                                                                                                                                                      ) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                                                     )
                                                                                                                                                                                                                                                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                                                  ))
                                                                                                                                                                                                                                                                                                                                                                                                                                  (and
                                                                                                                                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                     %%location_label%%103
                                                                                                                                                                                                                                                                                                                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_103_0~8102@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                                       temp_103_1~8127@
                                                                                                                                                                                                                                                                                                                                                                                                                                   ))))
                                                                                                                                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_103_0~8102@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                                      temp_103_1~8127@
                                                                                                                                                                                                                                                                                                                                                                                                                                    ))
                                                                                                                                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                     (= temp_104_0~8179@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                                                           (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                                                                                                                                                                                         ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                                                                                                                                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                                                                                                           (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                                                                                                                                                                                         ) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                                                     ))))
                                                                                                                                                                                                                                                                                                                                                                                                                                     (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                      (= temp_104_1~8209@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                                                            (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                                                           )
                                                                                                                                                                                                                                                                                                                                                                                                                                          ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                                                         )
                                                                                                                                                                                                                                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                                                                            (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                                                      ))))))
                                                                                                                                                                                                                                                                                                                                                                                                                                      (and
                                                                                                                                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                         %%location_label%%104
                                                                                                                                                                                                                                                                                                                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_104_0~8179@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                                           temp_104_1~8209@
                                                                                                                                                                                                                                                                                                                                                                                                                                       ))))
                                                                                                                                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_104_0~8179@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                                          temp_104_1~8209@
                                                                                                                                                                                                                                                                                                                                                                                                                                        ))
                                                                                                                                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                         (= temp_105_0~8256@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                                                                                                                                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                                                               (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                                                                                                                                                                                                             ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                                                         ))))
                                                                                                                                                                                                                                                                                                                                                                                                                                         (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                          (= temp_105_1~8281@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                                             (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                                               (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                                                   a~2@
                                                                                                                                                                                                                                                                                                                                                                                                                                                  ) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                 )
                                                                                                                                                                                                                                                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                                                          ))))))
                                                                                                                                                                                                                                                                                                                                                                                                                                          (and
                                                                                                                                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                             %%location_label%%105
                                                                                                                                                                                                                                                                                                                                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_105_0~8256@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                                               temp_105_1~8281@
                                                                                                                                                                                                                                                                                                                                                                                                                                           ))))
                                                                                                                                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_105_0~8256@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                                              temp_105_1~8281@
                                                                                                                                                                                                                                                                                                                                                                                                                                            ))
                                                                                                                                                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                             (= temp_106_0~8318@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                                                (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                                                  a~2@
                                                                                                                                                                                                                                                                                                                                                                                                                                             )))))
                                                                                                                                                                                                                                                                                                                                                                                                                                             (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                              (= temp_106_1~8333@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                                                 (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                                                   c~6@
                                                                                                                                                                                                                                                                                                                                                                                                                                              )))))
                                                                                                                                                                                                                                                                                                                                                                                                                                              (and
                                                                                                                                                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                                 %%location_label%%106
                                                                                                                                                                                                                                                                                                                                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_106_0~8318@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                                                   temp_106_1~8333@
                                                                                                                                                                                                                                                                                                                                                                                                                                               ))))
                                                                                                                                                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_106_0~8318@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                                                  temp_106_1~8333@
                                                                                                                                                                                                                                                                                                                                                                                                                                                ))
                                                                                                                                                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                                 (= temp_107_0~8380@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                                                                                                                                                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                                                                                                                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                                                                                                                       (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                                                                                                                                                                                                     ) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                 ))))
                                                                                                                                                                                                                                                                                                                                                                                                                                                 (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                                  (= temp_107_1~8430@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                                                                                                                                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                     )
                                                                                                                                                                                                                                                                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                                                                                                                        (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                               )
                                                                                                                                                                                                                                                                                                                                                                                                                                                              ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                             )))
                                                                                                                                                                                                                                                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                         )))
                                                                                                                                                                                                                                                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                       )
                                                                                                                                                                                                                                                                                                                                                                                                                                                      ) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                  ))))
                                                                                                                                                                                                                                                                                                                                                                                                                                                  (and
                                                                                                                                                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                                     %%location_label%%107
                                                                                                                                                                                                                                                                                                                                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_107_0~8380@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                                                       temp_107_1~8430@
                                                                                                                                                                                                                                                                                                                                                                                                                                                   ))))
                                                                                                                                                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_107_0~8380@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                                                      temp_107_1~8430@
                                                                                                                                                                                                                                                                                                                                                                                                                                                    ))
                                                                                                                                                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                                     (= temp_108_0~8472@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                                                                                                                                                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                     ))))
                                                                                                                                                                                                                                                                                                                                                                                                                                                     (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                                      (= temp_108_1~8492@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                         )
                                                                                                                                                                                                                                                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                      ))))
                                                                                                                                                                                                                                                                                                                                                                                                                                                      (and
                                                                                                                                                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                                         %%location_label%%108
                                                                                                                                                                                                                                                                                                                                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_108_0~8472@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                                                           temp_108_1~8492@
                                                                                                                                                                                                                                                                                                                                                                                                                                                       ))))
                                                                                                                                                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_108_0~8472@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                                                          temp_108_1~8492@
                                                                                                                                                                                                                                                                                                                                                                                                                                                        ))
                                                                                                                                                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                                         (= temp_109_0~8539@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                               (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                                                                                                                                                                                                                             ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                                                                                                                                                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                         ))))
                                                                                                                                                                                                                                                                                                                                                                                                                                                         (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                                          (= temp_109_1~8589@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                 )
                                                                                                                                                                                                                                                                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                                                                                    (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                     )
                                                                                                                                                                                                                                                                                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                   )))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                  ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                               )))
                                                                                                                                                                                                                                                                                                                                                                                                                                                              ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                             )
                                                                                                                                                                                                                                                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                          ))))
                                                                                                                                                                                                                                                                                                                                                                                                                                                          (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                                           (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                                            %%location_label%%109
                                                                                                                                                                                                                                                                                                                                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_109_0~8539@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                                                              temp_109_1~8589@
 )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
 (get-info :version)
 (assert
  %%query%%
 )
 (set-option :rlimit 4294967295)
 (check-sat)
