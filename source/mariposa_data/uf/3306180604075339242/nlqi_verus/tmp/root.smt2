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
       :pattern ((main!nl_basics.eq_.? y~988$ z~990$) (main!nl_basics.eq_.? x~986$ z~990$))
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
;; mariposa_data/uf//3306180604075339242/nlqi_verus/src/main.rs:7:1: 7:65 (#0)
(push)
 (declare-const a~2@ main!nl_basics.Elem.)
 (declare-const b~4@ main!nl_basics.Elem.)
 (declare-const c~6@ main!nl_basics.Elem.)
 (declare-const d~8@ main!nl_basics.Elem.)
 (declare-const m~10@ main!nl_basics.Elem.)
 (declare-const temp_0_0~35@ main!nl_basics.Elem.)
 (declare-const temp_0_1~92@ main!nl_basics.Elem.)
 (declare-const temp_1_0~134@ main!nl_basics.Elem.)
 (declare-const temp_1_1~164@ main!nl_basics.Elem.)
 (declare-const temp_2_0~211@ main!nl_basics.Elem.)
 (declare-const temp_2_1~266@ main!nl_basics.Elem.)
 (declare-const temp_3_0~308@ main!nl_basics.Elem.)
 (declare-const temp_3_1~328@ main!nl_basics.Elem.)
 (declare-const temp_4_0~370@ main!nl_basics.Elem.)
 (declare-const temp_4_1~390@ main!nl_basics.Elem.)
 (declare-const temp_5_0~439@ main!nl_basics.Elem.)
 (declare-const temp_5_1~466@ main!nl_basics.Elem.)
 (declare-const temp_6_0~508@ main!nl_basics.Elem.)
 (declare-const temp_6_1~528@ main!nl_basics.Elem.)
 (declare-const temp_7_0~570@ main!nl_basics.Elem.)
 (declare-const temp_7_1~615@ main!nl_basics.Elem.)
 (declare-const temp_8_0~662@ main!nl_basics.Elem.)
 (declare-const temp_8_1~712@ main!nl_basics.Elem.)
 (declare-const temp_9_0~754@ main!nl_basics.Elem.)
 (declare-const temp_9_1~774@ main!nl_basics.Elem.)
 (declare-const temp_10_0~821@ main!nl_basics.Elem.)
 (declare-const temp_10_1~846@ main!nl_basics.Elem.)
 (declare-const temp_11_0~888@ main!nl_basics.Elem.)
 (declare-const temp_11_1~908@ main!nl_basics.Elem.)
 (declare-const temp_12_0~950@ main!nl_basics.Elem.)
 (declare-const temp_12_1~970@ main!nl_basics.Elem.)
 (declare-const temp_13_0~1027@ main!nl_basics.Elem.)
 (declare-const temp_13_1~1092@ main!nl_basics.Elem.)
 (declare-const temp_14_0~1144@ main!nl_basics.Elem.)
 (declare-const temp_14_1~1174@ main!nl_basics.Elem.)
 (declare-const temp_15_0~1226@ main!nl_basics.Elem.)
 (declare-const temp_15_1~1291@ main!nl_basics.Elem.)
 (declare-const temp_16_0~1338@ main!nl_basics.Elem.)
 (declare-const temp_16_1~1388@ main!nl_basics.Elem.)
 (declare-const temp_17_0~1430@ main!nl_basics.Elem.)
 (declare-const temp_17_1~1450@ main!nl_basics.Elem.)
 (declare-const temp_18_0~1492@ main!nl_basics.Elem.)
 (declare-const temp_18_1~1512@ main!nl_basics.Elem.)
 (declare-const temp_19_0~1554@ main!nl_basics.Elem.)
 (declare-const temp_19_1~1574@ main!nl_basics.Elem.)
 (declare-const temp_20_0~1626@ main!nl_basics.Elem.)
 (declare-const temp_20_1~1656@ main!nl_basics.Elem.)
 (declare-const temp_21_0~1703@ main!nl_basics.Elem.)
 (declare-const temp_21_1~1758@ main!nl_basics.Elem.)
 (declare-const temp_22_0~1800@ main!nl_basics.Elem.)
 (declare-const temp_22_1~1820@ main!nl_basics.Elem.)
 (declare-const temp_23_0~1867@ main!nl_basics.Elem.)
 (declare-const temp_23_1~1922@ main!nl_basics.Elem.)
 (declare-const temp_24_0~1969@ main!nl_basics.Elem.)
 (declare-const temp_24_1~2029@ main!nl_basics.Elem.)
 (declare-const temp_25_0~2081@ main!nl_basics.Elem.)
 (declare-const temp_25_1~2148@ main!nl_basics.Elem.)
 (declare-const temp_26_0~2195@ main!nl_basics.Elem.)
 (declare-const temp_26_1~2220@ main!nl_basics.Elem.)
 (declare-const temp_27_0~2267@ main!nl_basics.Elem.)
 (declare-const temp_27_1~2292@ main!nl_basics.Elem.)
 (declare-const temp_28_0~2334@ main!nl_basics.Elem.)
 (declare-const temp_28_1~2354@ main!nl_basics.Elem.)
 (declare-const temp_29_0~2396@ main!nl_basics.Elem.)
 (declare-const temp_29_1~2416@ main!nl_basics.Elem.)
 (declare-const temp_30_0~2468@ main!nl_basics.Elem.)
 (declare-const temp_30_1~2530@ main!nl_basics.Elem.)
 (declare-const temp_31_0~2577@ main!nl_basics.Elem.)
 (declare-const temp_31_1~2617@ main!nl_basics.Elem.)
 (declare-const temp_32_0~2669@ main!nl_basics.Elem.)
 (declare-const temp_32_1~2699@ main!nl_basics.Elem.)
 (declare-const temp_33_0~2751@ main!nl_basics.Elem.)
 (declare-const temp_33_1~2801@ main!nl_basics.Elem.)
 (declare-const temp_34_0~2853@ main!nl_basics.Elem.)
 (declare-const temp_34_1~2893@ main!nl_basics.Elem.)
 (declare-const temp_35_0~2935@ main!nl_basics.Elem.)
 (declare-const temp_35_1~2955@ main!nl_basics.Elem.)
 (declare-const temp_36_0~2992@ main!nl_basics.Elem.)
 (declare-const temp_36_1~3007@ main!nl_basics.Elem.)
 (declare-const temp_37_0~3054@ main!nl_basics.Elem.)
 (declare-const temp_37_1~3079@ main!nl_basics.Elem.)
 (declare-const temp_38_0~3126@ main!nl_basics.Elem.)
 (declare-const temp_38_1~3151@ main!nl_basics.Elem.)
 (declare-const temp_39_0~3198@ main!nl_basics.Elem.)
 (declare-const temp_39_1~3223@ main!nl_basics.Elem.)
 (declare-const temp_40_0~3280@ main!nl_basics.Elem.)
 (declare-const temp_40_1~3315@ main!nl_basics.Elem.)
 (declare-const temp_41_0~3357@ main!nl_basics.Elem.)
 (declare-const temp_41_1~3377@ main!nl_basics.Elem.)
 (declare-const temp_42_0~3419@ main!nl_basics.Elem.)
 (declare-const temp_42_1~3439@ main!nl_basics.Elem.)
 (declare-const temp_43_0~3491@ main!nl_basics.Elem.)
 (declare-const temp_43_1~3521@ main!nl_basics.Elem.)
 (declare-const temp_44_0~3558@ main!nl_basics.Elem.)
 (declare-const temp_44_1~3578@ main!nl_basics.Elem.)
 (declare-const temp_45_0~3620@ main!nl_basics.Elem.)
 (declare-const temp_45_1~3640@ main!nl_basics.Elem.)
 (declare-const temp_46_0~3682@ main!nl_basics.Elem.)
 (declare-const temp_46_1~3702@ main!nl_basics.Elem.)
 (declare-const temp_47_0~3749@ main!nl_basics.Elem.)
 (declare-const temp_47_1~3774@ main!nl_basics.Elem.)
 (declare-const temp_48_0~3816@ main!nl_basics.Elem.)
 (declare-const temp_48_1~3836@ main!nl_basics.Elem.)
 (declare-const temp_49_0~3878@ main!nl_basics.Elem.)
 (declare-const temp_49_1~3898@ main!nl_basics.Elem.)
 (declare-const temp_50_0~3945@ main!nl_basics.Elem.)
 (declare-const temp_50_1~3970@ main!nl_basics.Elem.)
 (declare-const temp_51_0~4012@ main!nl_basics.Elem.)
 (declare-const temp_51_1~4032@ main!nl_basics.Elem.)
 (declare-const temp_52_0~4079@ main!nl_basics.Elem.)
 (declare-const temp_52_1~4134@ main!nl_basics.Elem.)
 (declare-const temp_53_0~4181@ main!nl_basics.Elem.)
 (declare-const temp_53_1~4206@ main!nl_basics.Elem.)
 (declare-const temp_54_0~4243@ main!nl_basics.Elem.)
 (declare-const temp_54_1~4258@ main!nl_basics.Elem.)
 (declare-const temp_55_0~4305@ main!nl_basics.Elem.)
 (declare-const temp_55_1~4355@ main!nl_basics.Elem.)
 (declare-const temp_56_0~4397@ main!nl_basics.Elem.)
 (declare-const temp_56_1~4417@ main!nl_basics.Elem.)
 (declare-const temp_57_0~4459@ main!nl_basics.Elem.)
 (declare-const temp_57_1~4479@ main!nl_basics.Elem.)
 (declare-const temp_58_0~4521@ main!nl_basics.Elem.)
 (declare-const temp_58_1~4541@ main!nl_basics.Elem.)
 (declare-const temp_59_0~4588@ main!nl_basics.Elem.)
 (declare-const temp_59_1~4623@ main!nl_basics.Elem.)
 (declare-const temp_60_0~4665@ main!nl_basics.Elem.)
 (declare-const temp_60_1~4685@ main!nl_basics.Elem.)
 (declare-const temp_61_0~4727@ main!nl_basics.Elem.)
 (declare-const temp_61_1~4747@ main!nl_basics.Elem.)
 (declare-const temp_62_0~4794@ main!nl_basics.Elem.)
 (declare-const temp_62_1~4854@ main!nl_basics.Elem.)
 (declare-const temp_63_0~4896@ main!nl_basics.Elem.)
 (declare-const temp_63_1~4916@ main!nl_basics.Elem.)
 (declare-const temp_64_0~4958@ main!nl_basics.Elem.)
 (declare-const temp_64_1~4978@ main!nl_basics.Elem.)
 (declare-const temp_65_0~5025@ main!nl_basics.Elem.)
 (declare-const temp_65_1~5050@ main!nl_basics.Elem.)
 (declare-const temp_66_0~5092@ main!nl_basics.Elem.)
 (declare-const temp_66_1~5122@ main!nl_basics.Elem.)
 (declare-const temp_67_0~5164@ main!nl_basics.Elem.)
 (declare-const temp_67_1~5184@ main!nl_basics.Elem.)
 (declare-const temp_68_0~5226@ main!nl_basics.Elem.)
 (declare-const temp_68_1~5246@ main!nl_basics.Elem.)
 (declare-const temp_69_0~5288@ main!nl_basics.Elem.)
 (declare-const temp_69_1~5308@ main!nl_basics.Elem.)
 (declare-const temp_70_0~5355@ main!nl_basics.Elem.)
 (declare-const temp_70_1~5380@ main!nl_basics.Elem.)
 (declare-const temp_71_0~5422@ main!nl_basics.Elem.)
 (declare-const temp_71_1~5442@ main!nl_basics.Elem.)
 (declare-const temp_72_0~5484@ main!nl_basics.Elem.)
 (declare-const temp_72_1~5504@ main!nl_basics.Elem.)
 (declare-const temp_73_0~5546@ main!nl_basics.Elem.)
 (declare-const temp_73_1~5566@ main!nl_basics.Elem.)
 (declare-const temp_74_0~5608@ main!nl_basics.Elem.)
 (declare-const temp_74_1~5628@ main!nl_basics.Elem.)
 (declare-const temp_75_0~5670@ main!nl_basics.Elem.)
 (declare-const temp_75_1~5690@ main!nl_basics.Elem.)
 (declare-const temp_76_0~5732@ main!nl_basics.Elem.)
 (declare-const temp_76_1~5752@ main!nl_basics.Elem.)
 (declare-const temp_77_0~5816@ main!nl_basics.Elem.)
 (declare-const temp_77_1~5858@ main!nl_basics.Elem.)
 (declare-const temp_78_0~5900@ main!nl_basics.Elem.)
 (declare-const temp_78_1~5920@ main!nl_basics.Elem.)
 (declare-const temp_79_0~5962@ main!nl_basics.Elem.)
 (declare-const temp_79_1~5982@ main!nl_basics.Elem.)
 (declare-const temp_80_0~6024@ main!nl_basics.Elem.)
 (declare-const temp_80_1~6044@ main!nl_basics.Elem.)
 (declare-const temp_81_0~6098@ main!nl_basics.Elem.)
 (declare-const temp_81_1~6130@ main!nl_basics.Elem.)
 (declare-const temp_82_0~6172@ main!nl_basics.Elem.)
 (declare-const temp_82_1~6192@ main!nl_basics.Elem.)
 (declare-const temp_83_0~6239@ main!nl_basics.Elem.)
 (declare-const temp_83_1~6294@ main!nl_basics.Elem.)
 (declare-const temp_84_0~6343@ main!nl_basics.Elem.)
 (declare-const temp_84_1~6370@ main!nl_basics.Elem.)
 (declare-const temp_85_0~6417@ main!nl_basics.Elem.)
 (declare-const temp_85_1~6467@ main!nl_basics.Elem.)
 (declare-const temp_86_0~6514@ main!nl_basics.Elem.)
 (declare-const temp_86_1~6564@ main!nl_basics.Elem.)
 (declare-const temp_87_0~6611@ main!nl_basics.Elem.)
 (declare-const temp_87_1~6661@ main!nl_basics.Elem.)
 (declare-const temp_88_0~6708@ main!nl_basics.Elem.)
 (declare-const temp_88_1~6733@ main!nl_basics.Elem.)
 (declare-const temp_89_0~6780@ main!nl_basics.Elem.)
 (declare-const temp_89_1~6805@ main!nl_basics.Elem.)
 (declare-const temp_90_0~6852@ main!nl_basics.Elem.)
 (declare-const temp_90_1~6902@ main!nl_basics.Elem.)
 (declare-const temp_91_0~6944@ main!nl_basics.Elem.)
 (declare-const temp_91_1~6964@ main!nl_basics.Elem.)
 (declare-const temp_92_0~7006@ main!nl_basics.Elem.)
 (declare-const temp_92_1~7026@ main!nl_basics.Elem.)
 (declare-const temp_93_0~7073@ main!nl_basics.Elem.)
 (declare-const temp_93_1~7098@ main!nl_basics.Elem.)
 (declare-const temp_94_0~7145@ main!nl_basics.Elem.)
 (declare-const temp_94_1~7170@ main!nl_basics.Elem.)
 (declare-const temp_95_0~7212@ main!nl_basics.Elem.)
 (declare-const temp_95_1~7232@ main!nl_basics.Elem.)
 (declare-const temp_96_0~7279@ main!nl_basics.Elem.)
 (declare-const temp_96_1~7319@ main!nl_basics.Elem.)
 (declare-const temp_97_0~7361@ main!nl_basics.Elem.)
 (declare-const temp_97_1~7381@ main!nl_basics.Elem.)
 (declare-const temp_98_0~7423@ main!nl_basics.Elem.)
 (declare-const temp_98_1~7443@ main!nl_basics.Elem.)
 (declare-const temp_99_0~7490@ main!nl_basics.Elem.)
 (declare-const temp_99_1~7545@ main!nl_basics.Elem.)
 (declare-const temp_100_0~7587@ main!nl_basics.Elem.)
 (declare-const temp_100_1~7607@ main!nl_basics.Elem.)
 (declare-const temp_101_0~7654@ main!nl_basics.Elem.)
 (declare-const temp_101_1~7704@ main!nl_basics.Elem.)
 (declare-const temp_102_0~7753@ main!nl_basics.Elem.)
 (declare-const temp_102_1~7780@ main!nl_basics.Elem.)
 (declare-const temp_103_0~7827@ main!nl_basics.Elem.)
 (declare-const temp_103_1~7889@ main!nl_basics.Elem.)
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
 (declare-const %%query%% Bool)
 (assert
  (=>
   %%query%%
   (not (=>
     (= temp_0_0~35@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
         (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. d~8@)
        )
       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
           (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. b~4@)
          )
         ) (Poly%main!nl_basics.Elem. m~10@)
     ))))
     (=>
      (= temp_0_1~92@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
          (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. d~8@)
         )
        ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
            (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.as_elem.?
                    (I 80)
                   )
                  ) (Poly%main!nl_basics.Elem. b~4@)
                 )
                ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                  (Poly%main!nl_basics.Elem. d~8@)
               )))
              ) (Poly%main!nl_basics.Elem. m~10@)
             )
            ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
              (Poly%main!nl_basics.Elem. b~4@)
           )))
          ) (Poly%main!nl_basics.Elem. m~10@)
      ))))
      (and
       (=>
        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
        (=>
         %%location_label%%0
         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_0_0~35@) (Poly%main!nl_basics.Elem.
           temp_0_1~92@
       ))))
       (=>
        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_0_0~35@) (Poly%main!nl_basics.Elem.
          temp_0_1~92@
        ))
        (=>
         (= temp_1_0~134@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
             (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. b~4@)
            )
           ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. d~8@)
             (Poly%main!nl_basics.Elem. d~8@)
         ))))
         (=>
          (= temp_1_1~164@ (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
              (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                (Poly%main!nl_basics.Elem. b~4@)
               )
              ) (Poly%main!nl_basics.Elem. d~8@)
             )
            ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. b~4@)
               )
              ) (Poly%main!nl_basics.Elem. d~8@)
          ))))
          (and
           (=>
            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
            (=>
             %%location_label%%1
             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_1_0~134@) (Poly%main!nl_basics.Elem.
               temp_1_1~164@
           ))))
           (=>
            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_1_0~134@) (Poly%main!nl_basics.Elem.
              temp_1_1~164@
            ))
            (=>
             (= temp_2_0~211@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                 (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. c~6@)
                )
               ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                   (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. d~8@)
                  )
                 ) (Poly%main!nl_basics.Elem. m~10@)
             ))))
             (=>
              (= temp_2_1~266@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                  (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. c~6@)
                 )
                ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                    (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                        (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                            (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. c~6@)
                           )
                          ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                            (Poly%main!nl_basics.Elem. d~8@)
                         )))
                        ) (Poly%main!nl_basics.Elem. m~10@)
                       )
                      ) (Poly%main!nl_basics.Elem. m~10@)
                     )
                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. a~2@)
                      (Poly%main!nl_basics.Elem. d~8@)
                   )))
                  ) (Poly%main!nl_basics.Elem. m~10@)
              ))))
              (and
               (=>
                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                (=>
                 %%location_label%%2
                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_2_0~211@) (Poly%main!nl_basics.Elem.
                   temp_2_1~266@
               ))))
               (=>
                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_2_0~211@) (Poly%main!nl_basics.Elem.
                  temp_2_1~266@
                ))
                (=>
                 (= temp_3_0~308@ (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                     (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. b~4@)
                    )
                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                     (Poly%main!nl_basics.Elem. c~6@)
                 ))))
                 (=>
                  (= temp_3_1~328@ (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                      (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. c~6@)
                     )
                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                      (Poly%main!nl_basics.Elem. b~4@)
                  ))))
                  (and
                   (=>
                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                    (=>
                     %%location_label%%3
                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_3_0~308@) (Poly%main!nl_basics.Elem.
                       temp_3_1~328@
                   ))))
                   (=>
                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_3_0~308@) (Poly%main!nl_basics.Elem.
                      temp_3_1~328@
                    ))
                    (=>
                     (= temp_4_0~370@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                         (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. a~2@)
                        )
                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. b~4@)
                         (Poly%main!nl_basics.Elem. d~8@)
                     ))))
                     (=>
                      (= temp_4_1~390@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                          (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. a~2@)
                         )
                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. b~4@)
                          (Poly%main!nl_basics.Elem. d~8@)
                      ))))
                      (and
                       (=>
                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                        (=>
                         %%location_label%%4
                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_4_0~370@) (Poly%main!nl_basics.Elem.
                           temp_4_1~390@
                       ))))
                       (=>
                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_4_0~370@) (Poly%main!nl_basics.Elem.
                          temp_4_1~390@
                        ))
                        (=>
                         (= temp_5_0~439@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                             (Poly%main!nl_basics.Elem. (main!nl_basics.as_elem.? (I 39))) (Poly%main!nl_basics.Elem.
                              d~8@
                            ))
                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                             (Poly%main!nl_basics.Elem. c~6@)
                         ))))
                         (=>
                          (= temp_5_1~466@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                              (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. c~6@)
                             )
                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.as_elem.?
                                (I 39)
                               )
                              ) (Poly%main!nl_basics.Elem. d~8@)
                          ))))
                          (and
                           (=>
                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                            (=>
                             %%location_label%%5
                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_5_0~439@) (Poly%main!nl_basics.Elem.
                               temp_5_1~466@
                           ))))
                           (=>
                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_5_0~439@) (Poly%main!nl_basics.Elem.
                              temp_5_1~466@
                            ))
                            (=>
                             (= temp_6_0~508@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                 (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. c~6@)
                                )
                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                 (Poly%main!nl_basics.Elem. c~6@)
                             ))))
                             (=>
                              (= temp_6_1~528@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem.
                                 (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem.
                                   (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem.
                                     c~6@
                              )))))))
                              (and
                               (=>
                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                (=>
                                 %%location_label%%6
                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_6_0~508@) (Poly%main!nl_basics.Elem.
                                   temp_6_1~528@
                               ))))
                               (=>
                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_6_0~508@) (Poly%main!nl_basics.Elem.
                                  temp_6_1~528@
                                ))
                                (=>
                                 (= temp_7_0~570@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                     (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. c~6@)
                                       (Poly%main!nl_basics.Elem. m~10@)
                                      )
                                     ) (Poly%main!nl_basics.Elem. a~2@)
                                    )
                                   ) (Poly%main!nl_basics.Elem. d~8@)
                                 ))
                                 (=>
                                  (= temp_7_1~615@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                      (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                          (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                            (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. c~6@)
                                               )
                                              ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                (Poly%main!nl_basics.Elem. c~6@)
                                             )))
                                            ) (Poly%main!nl_basics.Elem. m~10@)
                                         )))
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
                                     %%location_label%%7
                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_7_0~570@) (Poly%main!nl_basics.Elem.
                                       temp_7_1~615@
                                   ))))
                                   (=>
                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_7_0~570@) (Poly%main!nl_basics.Elem.
                                      temp_7_1~615@
                                    ))
                                    (=>
                                     (= temp_8_0~662@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                         (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. b~4@)
                                        )
                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                           (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. m~10@)
                                          )
                                         ) (Poly%main!nl_basics.Elem. a~2@)
                                     ))))
                                     (=>
                                      (= temp_8_1~712@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                          (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. b~4@)
                                         )
                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                            (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                    (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. b~4@)
                                                   )
                                                  ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                    (Poly%main!nl_basics.Elem. d~8@)
                                                 )))
                                                ) (Poly%main!nl_basics.Elem. m~10@)
                                               )
                                              ) (Poly%main!nl_basics.Elem. b~4@)
                                             )
                                            ) (Poly%main!nl_basics.Elem. m~10@)
                                           )
                                          ) (Poly%main!nl_basics.Elem. a~2@)
                                      ))))
                                      (and
                                       (=>
                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                        (=>
                                         %%location_label%%8
                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_8_0~662@) (Poly%main!nl_basics.Elem.
                                           temp_8_1~712@
                                       ))))
                                       (=>
                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_8_0~662@) (Poly%main!nl_basics.Elem.
                                          temp_8_1~712@
                                        ))
                                        (=>
                                         (= temp_9_0~754@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                             (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. c~6@)
                                            )
                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                             (Poly%main!nl_basics.Elem. c~6@)
                                         ))))
                                         (=>
                                          (= temp_9_1~774@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                              (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. c~6@)
                                             )
                                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. b~4@)
                                              (Poly%main!nl_basics.Elem. c~6@)
                                          ))))
                                          (and
                                           (=>
                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                            (=>
                                             %%location_label%%9
                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_9_0~754@) (Poly%main!nl_basics.Elem.
                                               temp_9_1~774@
                                           ))))
                                           (=>
                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_9_0~754@) (Poly%main!nl_basics.Elem.
                                              temp_9_1~774@
                                            ))
                                            (=>
                                             (= temp_10_0~821@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                 (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                   (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. m~10@)
                                                )))
                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. a~2@)
                                                 (Poly%main!nl_basics.Elem. b~4@)
                                             ))))
                                             (=>
                                              (= temp_10_1~846@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                  (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. c~6@)
                                                    (Poly%main!nl_basics.Elem. m~10@)
                                                   )
                                                  ) (Poly%main!nl_basics.Elem. a~2@)
                                                 )
                                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. a~2@)
                                                  (Poly%main!nl_basics.Elem. b~4@)
                                              ))))
                                              (and
                                               (=>
                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                (=>
                                                 %%location_label%%10
                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_10_0~821@) (Poly%main!nl_basics.Elem.
                                                   temp_10_1~846@
                                               ))))
                                               (=>
                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_10_0~821@) (Poly%main!nl_basics.Elem.
                                                  temp_10_1~846@
                                                ))
                                                (=>
                                                 (= temp_11_0~888@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                     (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. a~2@)
                                                    )
                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. b~4@)
                                                     (Poly%main!nl_basics.Elem. a~2@)
                                                 ))))
                                                 (=>
                                                  (= temp_11_1~908@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                      (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. a~2@)
                                                     )
                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. d~8@)
                                                      (Poly%main!nl_basics.Elem. a~2@)
                                                  ))))
                                                  (and
                                                   (=>
                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                    (=>
                                                     %%location_label%%11
                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_11_0~888@) (Poly%main!nl_basics.Elem.
                                                       temp_11_1~908@
                                                   ))))
                                                   (=>
                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_11_0~888@) (Poly%main!nl_basics.Elem.
                                                      temp_11_1~908@
                                                    ))
                                                    (=>
                                                     (= temp_12_0~950@ (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                         (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. b~4@)
                                                        )
                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                         (Poly%main!nl_basics.Elem. d~8@)
                                                     ))))
                                                     (=>
                                                      (= temp_12_1~970@ (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                          (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. d~8@)
                                                         )
                                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                          (Poly%main!nl_basics.Elem. d~8@)
                                                      ))))
                                                      (and
                                                       (=>
                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                        (=>
                                                         %%location_label%%12
                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_12_0~950@) (Poly%main!nl_basics.Elem.
                                                           temp_12_1~970@
                                                       ))))
                                                       (=>
                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_12_0~950@) (Poly%main!nl_basics.Elem.
                                                          temp_12_1~970@
                                                        ))
                                                        (=>
                                                         (= temp_13_0~1027@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                             (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                               (Poly%main!nl_basics.Elem. b~4@)
                                                              )
                                                             ) (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                 (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. m~10@)
                                                                )
                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                 (Poly%main!nl_basics.Elem. m~10@)
                                                            )))))
                                                           ) (Poly%main!nl_basics.Elem. m~10@)
                                                         ))
                                                         (=>
                                                          (= temp_13_1~1092@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                              (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                  (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. b~4@)
                                                                 )
                                                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                    (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. m~10@)
                                                                   )
                                                                  ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                    (Poly%main!nl_basics.Elem. m~10@)
                                                               )))))
                                                              ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                  (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                    (Poly%main!nl_basics.Elem. b~4@)
                                                                   )
                                                                  ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                    (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. a~2@)
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
                                                             %%location_label%%13
                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_13_0~1027@) (Poly%main!nl_basics.Elem.
                                                               temp_13_1~1092@
                                                           ))))
                                                           (=>
                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_13_0~1027@) (Poly%main!nl_basics.Elem.
                                                              temp_13_1~1092@
                                                            ))
                                                            (=>
                                                             (= temp_14_0~1144@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                 (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                   (Poly%main!nl_basics.Elem. d~8@)
                                                                  )
                                                                 ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                     (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. m~10@)
                                                                    )
                                                                   ) (Poly%main!nl_basics.Elem. b~4@)
                                                                )))
                                                               ) (Poly%main!nl_basics.Elem. m~10@)
                                                             ))
                                                             (=>
                                                              (= temp_14_1~1174@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                  (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                    (Poly%main!nl_basics.Elem. d~8@)
                                                                   )
                                                                  ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                    (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                      (Poly%main!nl_basics.Elem. m~10@)
                                                                 )))))
                                                                ) (Poly%main!nl_basics.Elem. m~10@)
                                                              ))
                                                              (and
                                                               (=>
                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                (=>
                                                                 %%location_label%%14
                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_14_0~1144@) (Poly%main!nl_basics.Elem.
                                                                   temp_14_1~1174@
                                                               ))))
                                                               (=>
                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_14_0~1144@) (Poly%main!nl_basics.Elem.
                                                                  temp_14_1~1174@
                                                                ))
                                                                (=>
                                                                 (= temp_15_0~1226@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                     (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                       (Poly%main!nl_basics.Elem. d~8@)
                                                                      )
                                                                     ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                         (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. d~8@)
                                                                        )
                                                                       ) (Poly%main!nl_basics.Elem. m~10@)
                                                                    )))
                                                                   ) (Poly%main!nl_basics.Elem. m~10@)
                                                                 ))
                                                                 (=>
                                                                  (= temp_15_1~1291@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                      (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                        (Poly%main!nl_basics.Elem. d~8@)
                                                                       )
                                                                      ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                          (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                              (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                  (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                 )
                                                                                ) (Poly%main!nl_basics.Elem. m~10@)
                                                                               )
                                                                              ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                  (Poly%main!nl_basics.Elem. m~10@)
                                                                             )))))
                                                                            ) (Poly%main!nl_basics.Elem. m~10@)
                                                                           )
                                                                          ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
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
                                                                     %%location_label%%15
                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_15_0~1226@) (Poly%main!nl_basics.Elem.
                                                                       temp_15_1~1291@
                                                                   ))))
                                                                   (=>
                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_15_0~1226@) (Poly%main!nl_basics.Elem.
                                                                      temp_15_1~1291@
                                                                    ))
                                                                    (=>
                                                                     (= temp_16_0~1338@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                         (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                           (Poly%main!nl_basics.Elem. d~8@)
                                                                          )
                                                                         ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                           (Poly%main!nl_basics.Elem. c~6@)
                                                                        )))
                                                                       ) (Poly%main!nl_basics.Elem. m~10@)
                                                                     ))
                                                                     (=>
                                                                      (= temp_16_1~1388@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                          (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                              (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. d~8@)
                                                                             )
                                                                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                              (Poly%main!nl_basics.Elem. c~6@)
                                                                           )))
                                                                          ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                              (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                (Poly%main!nl_basics.Elem. a~2@)
                                                                               )
                                                                              ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
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
                                                                         %%location_label%%16
                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_16_0~1338@) (Poly%main!nl_basics.Elem.
                                                                           temp_16_1~1388@
                                                                       ))))
                                                                       (=>
                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_16_0~1338@) (Poly%main!nl_basics.Elem.
                                                                          temp_16_1~1388@
                                                                        ))
                                                                        (=>
                                                                         (= temp_17_0~1430@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                             (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. c~6@)
                                                                            )
                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                             (Poly%main!nl_basics.Elem. d~8@)
                                                                         ))))
                                                                         (=>
                                                                          (= temp_17_1~1450@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem.
                                                                             (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem.
                                                                               (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem.
                                                                                 d~8@
                                                                          )))))))
                                                                          (and
                                                                           (=>
                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                            (=>
                                                                             %%location_label%%17
                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_17_0~1430@) (Poly%main!nl_basics.Elem.
                                                                               temp_17_1~1450@
                                                                           ))))
                                                                           (=>
                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_17_0~1430@) (Poly%main!nl_basics.Elem.
                                                                              temp_17_1~1450@
                                                                            ))
                                                                            (=>
                                                                             (= temp_18_0~1492@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                 (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                )
                                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                 (Poly%main!nl_basics.Elem. a~2@)
                                                                             ))))
                                                                             (=>
                                                                              (= temp_18_1~1512@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                  (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                    (Poly%main!nl_basics.Elem. a~2@)
                                                                                   )
                                                                                  ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                 )
                                                                                ) (Poly%main!nl_basics.Elem. a~2@)
                                                                              ))
                                                                              (and
                                                                               (=>
                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                (=>
                                                                                 %%location_label%%18
                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_18_0~1492@) (Poly%main!nl_basics.Elem.
                                                                                   temp_18_1~1512@
                                                                               ))))
                                                                               (=>
                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_18_0~1492@) (Poly%main!nl_basics.Elem.
                                                                                  temp_18_1~1512@
                                                                                ))
                                                                                (=>
                                                                                 (= temp_19_0~1554@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                     (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                    )
                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                     (Poly%main!nl_basics.Elem. b~4@)
                                                                                 ))))
                                                                                 (=>
                                                                                  (= temp_19_1~1574@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem.
                                                                                     (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem.
                                                                                       (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem.
                                                                                         b~4@
                                                                                  )))))))
                                                                                  (and
                                                                                   (=>
                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                    (=>
                                                                                     %%location_label%%19
                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_19_0~1554@) (Poly%main!nl_basics.Elem.
                                                                                       temp_19_1~1574@
                                                                                   ))))
                                                                                   (=>
                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_19_0~1554@) (Poly%main!nl_basics.Elem.
                                                                                      temp_19_1~1574@
                                                                                    ))
                                                                                    (=>
                                                                                     (= temp_20_0~1626@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                         (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                           (Poly%main!nl_basics.Elem. m~10@)
                                                                                          )
                                                                                         ) (Poly%main!nl_basics.Elem. a~2@)
                                                                                        )
                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                           (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                          )
                                                                                         ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                     ))))
                                                                                     (=>
                                                                                      (= temp_20_1~1656@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                          (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                         )
                                                                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                          (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                              (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                             )
                                                                                            ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                      ))))))
                                                                                      (and
                                                                                       (=>
                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                        (=>
                                                                                         %%location_label%%20
                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_20_0~1626@) (Poly%main!nl_basics.Elem.
                                                                                           temp_20_1~1656@
                                                                                       ))))
                                                                                       (=>
                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_20_0~1626@) (Poly%main!nl_basics.Elem.
                                                                                          temp_20_1~1656@
                                                                                        ))
                                                                                        (=>
                                                                                         (= temp_21_0~1703@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                             (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                            )
                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                             (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                               (Poly%main!nl_basics.Elem. m~10@)
                                                                                         ))))))
                                                                                         (=>
                                                                                          (= temp_21_1~1758@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                              (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                             )
                                                                                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                              (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                  (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                    (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                        (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                          (Poly%main!nl_basics.Elem. m~10@)
                                                                                                         )
                                                                                                        ) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                       )
                                                                                                      ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                        (Poly%main!nl_basics.Elem. b~4@)
                                                                                                     )))
                                                                                                    ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                 )))
                                                                                                ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                          ))))))
                                                                                          (and
                                                                                           (=>
                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                            (=>
                                                                                             %%location_label%%21
                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_21_0~1703@) (Poly%main!nl_basics.Elem.
                                                                                               temp_21_1~1758@
                                                                                           ))))
                                                                                           (=>
                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_21_0~1703@) (Poly%main!nl_basics.Elem.
                                                                                              temp_21_1~1758@
                                                                                            ))
                                                                                            (=>
                                                                                             (= temp_22_0~1800@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                 (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                )
                                                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                 (Poly%main!nl_basics.Elem. a~2@)
                                                                                             ))))
                                                                                             (=>
                                                                                              (= temp_22_1~1820@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                  (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                 )
                                                                                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                  (Poly%main!nl_basics.Elem. d~8@)
                                                                                              ))))
                                                                                              (and
                                                                                               (=>
                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                (=>
                                                                                                 %%location_label%%22
                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_22_0~1800@) (Poly%main!nl_basics.Elem.
                                                                                                   temp_22_1~1820@
                                                                                               ))))
                                                                                               (=>
                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_22_0~1800@) (Poly%main!nl_basics.Elem.
                                                                                                  temp_22_1~1820@
                                                                                                ))
                                                                                                (=>
                                                                                                 (= temp_23_0~1867@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                     (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                       (Poly%main!nl_basics.Elem. c~6@)
                                                                                                      )
                                                                                                     ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                       (Poly%main!nl_basics.Elem. d~8@)
                                                                                                    )))
                                                                                                   ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                 ))
                                                                                                 (=>
                                                                                                  (= temp_23_1~1922@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                                                      (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                          (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                            (Poly%main!nl_basics.Elem. b~4@)
                                                                                                           )
                                                                                                          ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                              (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                             )
                                                                                                            ) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                         )))
                                                                                                        ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                       )
                                                                                                      ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                          (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                         )
                                                                                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                          (Poly%main!nl_basics.Elem. d~8@)
                                                                                                     )))))
                                                                                                    ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                  ))
                                                                                                  (and
                                                                                                   (=>
                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                    (=>
                                                                                                     %%location_label%%23
                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_23_0~1867@) (Poly%main!nl_basics.Elem.
                                                                                                       temp_23_1~1922@
                                                                                                   ))))
                                                                                                   (=>
                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_23_0~1867@) (Poly%main!nl_basics.Elem.
                                                                                                      temp_23_1~1922@
                                                                                                    ))
                                                                                                    (=>
                                                                                                     (= temp_24_0~1969@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                         (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                        )
                                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                           (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                          )
                                                                                                         ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                     ))))
                                                                                                     (=>
                                                                                                      (= temp_24_1~2029@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                          (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                         )
                                                                                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                            (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                    (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                      (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                   )))
                                                                                                                  ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                      (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                     )
                                                                                                                    ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                 )))
                                                                                                                ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                               )
                                                                                                              ) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                             )
                                                                                                            ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                           )
                                                                                                          ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                      ))))
                                                                                                      (and
                                                                                                       (=>
                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                        (=>
                                                                                                         %%location_label%%24
                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_24_0~1969@) (Poly%main!nl_basics.Elem.
                                                                                                           temp_24_1~2029@
                                                                                                       ))))
                                                                                                       (=>
                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_24_0~1969@) (Poly%main!nl_basics.Elem.
                                                                                                          temp_24_1~2029@
                                                                                                        ))
                                                                                                        (=>
                                                                                                         (= temp_25_0~2081@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                             (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                               (Poly%main!nl_basics.Elem. m~10@)
                                                                                                              )
                                                                                                             ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                               (Poly%main!nl_basics.Elem. m~10@)
                                                                                                            )))
                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                             (Poly%main!nl_basics.Elem. d~8@)
                                                                                                         ))))
                                                                                                         (=>
                                                                                                          (= temp_25_1~2148@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                              (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                (Poly%main!nl_basics.Elem. m~10@)
                                                                                                               )
                                                                                                              ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                  (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                    (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                        (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. (main!nl_basics.as_elem.?
                                                                                                                          (I 48)
                                                                                                                       )))
                                                                                                                      ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                          (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. m~10@)
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
                                                                                                             %%location_label%%25
                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_25_0~2081@) (Poly%main!nl_basics.Elem.
                                                                                                               temp_25_1~2148@
                                                                                                           ))))
                                                                                                           (=>
                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_25_0~2081@) (Poly%main!nl_basics.Elem.
                                                                                                              temp_25_1~2148@
                                                                                                            ))
                                                                                                            (=>
                                                                                                             (= temp_26_0~2195@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                 (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                   (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                  )
                                                                                                                 ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                   (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                )))
                                                                                                               ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                             ))
                                                                                                             (=>
                                                                                                              (= temp_26_1~2220@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                  (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                    (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                   )
                                                                                                                  ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                    (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                 )))
                                                                                                                ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                              ))
                                                                                                              (and
                                                                                                               (=>
                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                (=>
                                                                                                                 %%location_label%%26
                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_26_0~2195@) (Poly%main!nl_basics.Elem.
                                                                                                                   temp_26_1~2220@
                                                                                                               ))))
                                                                                                               (=>
                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_26_0~2195@) (Poly%main!nl_basics.Elem.
                                                                                                                  temp_26_1~2220@
                                                                                                                ))
                                                                                                                (=>
                                                                                                                 (= temp_27_0~2267@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                     (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                    )
                                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                       (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                      )
                                                                                                                     ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                 ))))
                                                                                                                 (=>
                                                                                                                  (= temp_27_1~2292@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                      (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                        (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                       )
                                                                                                                      ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                     )
                                                                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                      (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                  ))))
                                                                                                                  (and
                                                                                                                   (=>
                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                    (=>
                                                                                                                     %%location_label%%27
                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_27_0~2267@) (Poly%main!nl_basics.Elem.
                                                                                                                       temp_27_1~2292@
                                                                                                                   ))))
                                                                                                                   (=>
                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_27_0~2267@) (Poly%main!nl_basics.Elem.
                                                                                                                      temp_27_1~2292@
                                                                                                                    ))
                                                                                                                    (=>
                                                                                                                     (= temp_28_0~2334@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                         (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                        )
                                                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                         (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                     ))))
                                                                                                                     (=>
                                                                                                                      (= temp_28_1~2354@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem.
                                                                                                                         (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem.
                                                                                                                           (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem.
                                                                                                                             a~2@
                                                                                                                      )))))))
                                                                                                                      (and
                                                                                                                       (=>
                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                        (=>
                                                                                                                         %%location_label%%28
                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_28_0~2334@) (Poly%main!nl_basics.Elem.
                                                                                                                           temp_28_1~2354@
                                                                                                                       ))))
                                                                                                                       (=>
                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_28_0~2334@) (Poly%main!nl_basics.Elem.
                                                                                                                          temp_28_1~2354@
                                                                                                                        ))
                                                                                                                        (=>
                                                                                                                         (= temp_29_0~2396@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                             (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                            )
                                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                             (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                         ))))
                                                                                                                         (=>
                                                                                                                          (= temp_29_1~2416@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                              (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                             )
                                                                                                                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                              (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                          ))))
                                                                                                                          (and
                                                                                                                           (=>
                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                            (=>
                                                                                                                             %%location_label%%29
                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_29_0~2396@) (Poly%main!nl_basics.Elem.
                                                                                                                               temp_29_1~2416@
                                                                                                                           ))))
                                                                                                                           (=>
                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_29_0~2396@) (Poly%main!nl_basics.Elem.
                                                                                                                              temp_29_1~2416@
                                                                                                                            ))
                                                                                                                            (=>
                                                                                                                             (= temp_30_0~2468@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                 (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                   (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                  )
                                                                                                                                 ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                   (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                )))
                                                                                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                 (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                             ))))
                                                                                                                             (=>
                                                                                                                              (= temp_30_1~2530@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                  (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                    (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                   )
                                                                                                                                  ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                                                                                      (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                          (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                            (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                           )
                                                                                                                                          ) (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.as_elem.?
                                                                                                                                              (I 65)
                                                                                                                                             )
                                                                                                                                            ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                         )))
                                                                                                                                        ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                       )
                                                                                                                                      ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                     )
                                                                                                                                    ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                 )))
                                                                                                                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                  (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                              ))))
                                                                                                                              (and
                                                                                                                               (=>
                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                (=>
                                                                                                                                 %%location_label%%30
                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_30_0~2468@) (Poly%main!nl_basics.Elem.
                                                                                                                                   temp_30_1~2530@
                                                                                                                               ))))
                                                                                                                               (=>
                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_30_0~2468@) (Poly%main!nl_basics.Elem.
                                                                                                                                  temp_30_1~2530@
                                                                                                                                ))
                                                                                                                                (=>
                                                                                                                                 (= temp_31_0~2577@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                                                                                     (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                    )
                                                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                       (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                      )
                                                                                                                                     ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                 ))))
                                                                                                                                 (=>
                                                                                                                                  (= temp_31_1~2617@ (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                      (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                        (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                          (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                         )
                                                                                                                                        ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                     )))
                                                                                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                      (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                          (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                         )
                                                                                                                                        ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                  ))))))
                                                                                                                                  (and
                                                                                                                                   (=>
                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                    (=>
                                                                                                                                     %%location_label%%31
                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_31_0~2577@) (Poly%main!nl_basics.Elem.
                                                                                                                                       temp_31_1~2617@
                                                                                                                                   ))))
                                                                                                                                   (=>
                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_31_0~2577@) (Poly%main!nl_basics.Elem.
                                                                                                                                      temp_31_1~2617@
                                                                                                                                    ))
                                                                                                                                    (=>
                                                                                                                                     (= temp_32_0~2669@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                         (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                        )
                                                                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                           (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                             (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                            )
                                                                                                                                           ) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                          )
                                                                                                                                         ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                     ))))
                                                                                                                                     (=>
                                                                                                                                      (= temp_32_1~2699@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem.
                                                                                                                                         (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem.
                                                                                                                                           (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem.
                                                                                                                                               (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem.
                                                                                                                                                 m~10@
                                                                                                                                               ))
                                                                                                                                              ) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                             )
                                                                                                                                            ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                      ))))))
                                                                                                                                      (and
                                                                                                                                       (=>
                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                        (=>
                                                                                                                                         %%location_label%%32
                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_32_0~2669@) (Poly%main!nl_basics.Elem.
                                                                                                                                           temp_32_1~2699@
                                                                                                                                       ))))
                                                                                                                                       (=>
                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_32_0~2669@) (Poly%main!nl_basics.Elem.
                                                                                                                                          temp_32_1~2699@
                                                                                                                                        ))
                                                                                                                                        (=>
                                                                                                                                         (= temp_33_0~2751@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                             (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                               (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                              )
                                                                                                                                             ) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                            )
                                                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                               (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                              )
                                                                                                                                             ) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                         ))))
                                                                                                                                         (=>
                                                                                                                                          (= temp_33_1~2801@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                              (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                                                  (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                    (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                        (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                       )
                                                                                                                                                      ) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                     )
                                                                                                                                                    ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                 )))
                                                                                                                                                ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                               )
                                                                                                                                              ) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                             )
                                                                                                                                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                               )
                                                                                                                                              ) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                          ))))
                                                                                                                                          (and
                                                                                                                                           (=>
                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                            (=>
                                                                                                                                             %%location_label%%33
                                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_33_0~2751@) (Poly%main!nl_basics.Elem.
                                                                                                                                               temp_33_1~2801@
                                                                                                                                           ))))
                                                                                                                                           (=>
                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_33_0~2751@) (Poly%main!nl_basics.Elem.
                                                                                                                                              temp_33_1~2801@
                                                                                                                                            ))
                                                                                                                                            (=>
                                                                                                                                             (= temp_34_0~2853@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                                                 (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                   (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                  )
                                                                                                                                                 ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                   (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                )))
                                                                                                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                 (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                             ))))
                                                                                                                                             (=>
                                                                                                                                              (= temp_34_1~2893@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                  (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                    (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                   )
                                                                                                                                                  ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                    (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                 )))
                                                                                                                                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                    (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                   )
                                                                                                                                                  ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                    (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                              ))))))
                                                                                                                                              (and
                                                                                                                                               (=>
                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                (=>
                                                                                                                                                 %%location_label%%34
                                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_34_0~2853@) (Poly%main!nl_basics.Elem.
                                                                                                                                                   temp_34_1~2893@
                                                                                                                                               ))))
                                                                                                                                               (=>
                                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_34_0~2853@) (Poly%main!nl_basics.Elem.
                                                                                                                                                  temp_34_1~2893@
                                                                                                                                                ))
                                                                                                                                                (=>
                                                                                                                                                 (= temp_35_0~2935@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                     (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                    )
                                                                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                     (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                 ))))
                                                                                                                                                 (=>
                                                                                                                                                  (= temp_35_1~2955@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                      (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                     )
                                                                                                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                      (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                  ))))
                                                                                                                                                  (and
                                                                                                                                                   (=>
                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                    (=>
                                                                                                                                                     %%location_label%%35
                                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_35_0~2935@) (Poly%main!nl_basics.Elem.
                                                                                                                                                       temp_35_1~2955@
                                                                                                                                                   ))))
                                                                                                                                                   (=>
                                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_35_0~2935@) (Poly%main!nl_basics.Elem.
                                                                                                                                                      temp_35_1~2955@
                                                                                                                                                    ))
                                                                                                                                                    (=>
                                                                                                                                                     (= temp_36_0~2992@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                         (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                        )
                                                                                                                                                       ) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                     ))
                                                                                                                                                     (=>
                                                                                                                                                      (= temp_36_1~3007@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                          (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                         )
                                                                                                                                                        ) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                      ))
                                                                                                                                                      (and
                                                                                                                                                       (=>
                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                        (=>
                                                                                                                                                         %%location_label%%36
                                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_36_0~2992@) (Poly%main!nl_basics.Elem.
                                                                                                                                                           temp_36_1~3007@
                                                                                                                                                       ))))
                                                                                                                                                       (=>
                                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_36_0~2992@) (Poly%main!nl_basics.Elem.
                                                                                                                                                          temp_36_1~3007@
                                                                                                                                                        ))
                                                                                                                                                        (=>
                                                                                                                                                         (= temp_37_0~3054@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                             (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                               (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                            )))
                                                                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                             (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                         ))))
                                                                                                                                                         (=>
                                                                                                                                                          (= temp_37_1~3079@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                              (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                  (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                               )))
                                                                                                                                                              ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                             )
                                                                                                                                                            ) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                          ))
                                                                                                                                                          (and
                                                                                                                                                           (=>
                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                            (=>
                                                                                                                                                             %%location_label%%37
                                                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_37_0~3054@) (Poly%main!nl_basics.Elem.
                                                                                                                                                               temp_37_1~3079@
                                                                                                                                                           ))))
                                                                                                                                                           (=>
                                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_37_0~3054@) (Poly%main!nl_basics.Elem.
                                                                                                                                                              temp_37_1~3079@
                                                                                                                                                            ))
                                                                                                                                                            (=>
                                                                                                                                                             (= temp_38_0~3126@ (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                                                                 (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                   (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                  )
                                                                                                                                                                 ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                )
                                                                                                                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                 (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                             ))))
                                                                                                                                                             (=>
                                                                                                                                                              (= temp_38_1~3151@ (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                  (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                 )
                                                                                                                                                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                    (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                   )
                                                                                                                                                                  ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                              ))))
                                                                                                                                                              (and
                                                                                                                                                               (=>
                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                (=>
                                                                                                                                                                 %%location_label%%38
                                                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_38_0~3126@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                   temp_38_1~3151@
                                                                                                                                                               ))))
                                                                                                                                                               (=>
                                                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_38_0~3126@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                  temp_38_1~3151@
                                                                                                                                                                ))
                                                                                                                                                                (=>
                                                                                                                                                                 (= temp_39_0~3198@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                                                                                                                     (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                       (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                      )
                                                                                                                                                                     ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                       (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                    )))
                                                                                                                                                                   ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                 ))
                                                                                                                                                                 (=>
                                                                                                                                                                  (= temp_39_1~3223@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                                                                                                                      (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                        (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                       )
                                                                                                                                                                      ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                        (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                     )))
                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                  ))
                                                                                                                                                                  (and
                                                                                                                                                                   (=>
                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                    (=>
                                                                                                                                                                     %%location_label%%39
                                                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_39_0~3198@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                       temp_39_1~3223@
                                                                                                                                                                   ))))
                                                                                                                                                                   (=>
                                                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_39_0~3198@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                      temp_39_1~3223@
                                                                                                                                                                    ))
                                                                                                                                                                    (=>
                                                                                                                                                                     (= temp_40_0~3280@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                         (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                           (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                          )
                                                                                                                                                                         ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                        )
                                                                                                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                           (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                          )
                                                                                                                                                                         ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                           (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                     ))))))
                                                                                                                                                                     (=>
                                                                                                                                                                      (= temp_40_1~3315@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                          (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                            (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                           )
                                                                                                                                                                          ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                         )
                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                            (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                           )
                                                                                                                                                                          ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                            (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                      ))))))
                                                                                                                                                                      (and
                                                                                                                                                                       (=>
                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                        (=>
                                                                                                                                                                         %%location_label%%40
                                                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_40_0~3280@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                           temp_40_1~3315@
                                                                                                                                                                       ))))
                                                                                                                                                                       (=>
                                                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_40_0~3280@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                          temp_40_1~3315@
                                                                                                                                                                        ))
                                                                                                                                                                        (=>
                                                                                                                                                                         (= temp_41_0~3357@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                             (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                            )
                                                                                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                             (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                         ))))
                                                                                                                                                                         (=>
                                                                                                                                                                          (= temp_41_1~3377@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                              (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                               )
                                                                                                                                                                              ) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                             )
                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                          ))
                                                                                                                                                                          (and
                                                                                                                                                                           (=>
                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                            (=>
                                                                                                                                                                             %%location_label%%41
                                                                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_41_0~3357@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                               temp_41_1~3377@
                                                                                                                                                                           ))))
                                                                                                                                                                           (=>
                                                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_41_0~3357@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                              temp_41_1~3377@
                                                                                                                                                                            ))
                                                                                                                                                                            (=>
                                                                                                                                                                             (= temp_42_0~3419@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                 (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                )
                                                                                                                                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                 (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                             ))))
                                                                                                                                                                             (=>
                                                                                                                                                                              (= temp_42_1~3439@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                 (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                   (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                     b~4@
                                                                                                                                                                              )))))))
                                                                                                                                                                              (and
                                                                                                                                                                               (=>
                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                (=>
                                                                                                                                                                                 %%location_label%%42
                                                                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_42_0~3419@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                   temp_42_1~3439@
                                                                                                                                                                               ))))
                                                                                                                                                                               (=>
                                                                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_42_0~3419@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                  temp_42_1~3439@
                                                                                                                                                                                ))
                                                                                                                                                                                (=>
                                                                                                                                                                                 (= temp_43_0~3491@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                     (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                       (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                    )))
                                                                                                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                       (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                      )
                                                                                                                                                                                     ) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                 ))))
                                                                                                                                                                                 (=>
                                                                                                                                                                                  (= temp_43_1~3521@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                     (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem.
                                                                                                                                                                                         c~6@
                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                       )
                                                                                                                                                                                      ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                          (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                         )
                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                  ))))))
                                                                                                                                                                                  (and
                                                                                                                                                                                   (=>
                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                    (=>
                                                                                                                                                                                     %%location_label%%43
                                                                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_43_0~3491@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                       temp_43_1~3521@
                                                                                                                                                                                   ))))
                                                                                                                                                                                   (=>
                                                                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_43_0~3491@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                      temp_43_1~3521@
                                                                                                                                                                                    ))
                                                                                                                                                                                    (=>
                                                                                                                                                                                     (= temp_44_0~3558@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                                                                                         (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                        )
                                                                                                                                                                                       ) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                     ))
                                                                                                                                                                                     (=>
                                                                                                                                                                                      (= temp_44_1~3578@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                          (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                         )
                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                          (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                      ))))
                                                                                                                                                                                      (and
                                                                                                                                                                                       (=>
                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                        (=>
                                                                                                                                                                                         %%location_label%%44
                                                                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_44_0~3558@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                           temp_44_1~3578@
                                                                                                                                                                                       ))))
                                                                                                                                                                                       (=>
                                                                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_44_0~3558@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                          temp_44_1~3578@
                                                                                                                                                                                        ))
                                                                                                                                                                                        (=>
                                                                                                                                                                                         (= temp_45_0~3620@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                             (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                            )
                                                                                                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                             (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                         ))))
                                                                                                                                                                                         (=>
                                                                                                                                                                                          (= temp_45_1~3640@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                              (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                             )
                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                              (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                          ))))
                                                                                                                                                                                          (and
                                                                                                                                                                                           (=>
                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                            (=>
                                                                                                                                                                                             %%location_label%%45
                                                                                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_45_0~3620@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                               temp_45_1~3640@
                                                                                                                                                                                           ))))
                                                                                                                                                                                           (=>
                                                                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_45_0~3620@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                              temp_45_1~3640@
                                                                                                                                                                                            ))
                                                                                                                                                                                            (=>
                                                                                                                                                                                             (= temp_46_0~3682@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                )
                                                                                                                                                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                             ))))
                                                                                                                                                                                             (=>
                                                                                                                                                                                              (= temp_46_1~3702@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                 )
                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                              ))))
                                                                                                                                                                                              (and
                                                                                                                                                                                               (=>
                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                (=>
                                                                                                                                                                                                 %%location_label%%46
                                                                                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_46_0~3682@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                   temp_46_1~3702@
                                                                                                                                                                                               ))))
                                                                                                                                                                                               (=>
                                                                                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_46_0~3682@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                  temp_46_1~3702@
                                                                                                                                                                                                ))
                                                                                                                                                                                                (=>
                                                                                                                                                                                                 (= temp_47_0~3749@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                       (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                    )))
                                                                                                                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                 ))))
                                                                                                                                                                                                 (=>
                                                                                                                                                                                                  (= temp_47_1~3774@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                        (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                       )))
                                                                                                                                                                                                      ) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                     )
                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                  ))
                                                                                                                                                                                                  (and
                                                                                                                                                                                                   (=>
                                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                    (=>
                                                                                                                                                                                                     %%location_label%%47
                                                                                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_47_0~3749@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                       temp_47_1~3774@
                                                                                                                                                                                                   ))))
                                                                                                                                                                                                   (=>
                                                                                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_47_0~3749@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                      temp_47_1~3774@
                                                                                                                                                                                                    ))
                                                                                                                                                                                                    (=>
                                                                                                                                                                                                     (= temp_48_0~3816@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                        )
                                                                                                                                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                     ))))
                                                                                                                                                                                                     (=>
                                                                                                                                                                                                      (= temp_48_1~3836@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                         )
                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                      ))))
                                                                                                                                                                                                      (and
                                                                                                                                                                                                       (=>
                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                        (=>
                                                                                                                                                                                                         %%location_label%%48
                                                                                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_48_0~3816@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                           temp_48_1~3836@
                                                                                                                                                                                                       ))))
                                                                                                                                                                                                       (=>
                                                                                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_48_0~3816@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                          temp_48_1~3836@
                                                                                                                                                                                                        ))
                                                                                                                                                                                                        (=>
                                                                                                                                                                                                         (= temp_49_0~3878@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                            )
                                                                                                                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                         ))))
                                                                                                                                                                                                         (=>
                                                                                                                                                                                                          (= temp_49_1~3898@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                             )
                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                          ))))
                                                                                                                                                                                                          (and
                                                                                                                                                                                                           (=>
                                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                            (=>
                                                                                                                                                                                                             %%location_label%%49
                                                                                                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_49_0~3878@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                               temp_49_1~3898@
                                                                                                                                                                                                           ))))
                                                                                                                                                                                                           (=>
                                                                                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_49_0~3878@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                              temp_49_1~3898@
                                                                                                                                                                                                            ))
                                                                                                                                                                                                            (=>
                                                                                                                                                                                                             (= temp_50_0~3945@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                   (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                  )
                                                                                                                                                                                                                 ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                   (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                )))
                                                                                                                                                                                                               ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                             ))
                                                                                                                                                                                                             (=>
                                                                                                                                                                                                              (= temp_50_1~3970@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                    (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                   )
                                                                                                                                                                                                                  ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                    (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                 )))
                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                              ))
                                                                                                                                                                                                              (and
                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                 %%location_label%%50
                                                                                                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_50_0~3945@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                   temp_50_1~3970@
                                                                                                                                                                                                               ))))
                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_50_0~3945@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                  temp_50_1~3970@
                                                                                                                                                                                                                ))
                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                 (= temp_51_0~4012@ (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                    )
                                                                                                                                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                 ))))
                                                                                                                                                                                                                 (=>
                                                                                                                                                                                                                  (= temp_51_1~4032@ (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                     )
                                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                  ))))
                                                                                                                                                                                                                  (and
                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                     %%location_label%%51
                                                                                                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_51_0~4012@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                       temp_51_1~4032@
                                                                                                                                                                                                                   ))))
                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_51_0~4012@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                      temp_51_1~4032@
                                                                                                                                                                                                                    ))
                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                     (= temp_52_0~4079@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                        )
                                                                                                                                                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                           (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                     ))))))
                                                                                                                                                                                                                     (=>
                                                                                                                                                                                                                      (= temp_52_1~4134@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                         )
                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                                                                                                                                    (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                   )))
                                                                                                                                                                                                                                  ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                    (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                 )))
                                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                             )))
                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                      ))))))
                                                                                                                                                                                                                      (and
                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                         %%location_label%%52
                                                                                                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_52_0~4079@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                           temp_52_1~4134@
                                                                                                                                                                                                                       ))))
                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_52_0~4079@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                          temp_52_1~4134@
                                                                                                                                                                                                                        ))
                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                         (= temp_53_0~4181@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                            )
                                                                                                                                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                               (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                              )
                                                                                                                                                                                                                             ) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                         ))))
                                                                                                                                                                                                                         (=>
                                                                                                                                                                                                                          (= temp_53_1~4206@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                             )
                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                               )
                                                                                                                                                                                                                              ) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                          ))))
                                                                                                                                                                                                                          (and
                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                             %%location_label%%53
                                                                                                                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_53_0~4181@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                               temp_53_1~4206@
                                                                                                                                                                                                                           ))))
                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_53_0~4181@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                              temp_53_1~4206@
                                                                                                                                                                                                                            ))
                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                             (= temp_54_0~4243@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                  a~2@
                                                                                                                                                                                                                             )))))
                                                                                                                                                                                                                             (=>
                                                                                                                                                                                                                              (= temp_54_1~4258@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                 )
                                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                              ))
                                                                                                                                                                                                                              (and
                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                 %%location_label%%54
                                                                                                                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_54_0~4243@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                   temp_54_1~4258@
                                                                                                                                                                                                                               ))))
                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_54_0~4243@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                  temp_54_1~4258@
                                                                                                                                                                                                                                ))
                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                 (= temp_55_0~4305@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                       (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                     ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                 ))))
                                                                                                                                                                                                                                 (=>
                                                                                                                                                                                                                                  (= temp_55_1~4355@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                     )
                                                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                                                                                                                                                                                        (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                                                                                                                                                                                            (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                             )
                                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                           )))
                                                                                                                                                                                                                                          ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                         )
                                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                       )))
                                                                                                                                                                                                                                      ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                  ))))
                                                                                                                                                                                                                                  (and
                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                     %%location_label%%55
                                                                                                                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_55_0~4305@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                       temp_55_1~4355@
                                                                                                                                                                                                                                   ))))
                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_55_0~4305@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                      temp_55_1~4355@
                                                                                                                                                                                                                                    ))
                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                     (= temp_56_0~4397@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                     ))))
                                                                                                                                                                                                                                     (=>
                                                                                                                                                                                                                                      (= temp_56_1~4417@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                         (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                           (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                             b~4@
                                                                                                                                                                                                                                      )))))))
                                                                                                                                                                                                                                      (and
                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                         %%location_label%%56
                                                                                                                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_56_0~4397@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                           temp_56_1~4417@
                                                                                                                                                                                                                                       ))))
                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_56_0~4397@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                          temp_56_1~4417@
                                                                                                                                                                                                                                        ))
                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                         (= temp_57_0~4459@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                         ))))
                                                                                                                                                                                                                                         (=>
                                                                                                                                                                                                                                          (= temp_57_1~4479@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                               )
                                                                                                                                                                                                                                              ) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                             )
                                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                          ))
                                                                                                                                                                                                                                          (and
                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                             %%location_label%%57
                                                                                                                                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_57_0~4459@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                               temp_57_1~4479@
                                                                                                                                                                                                                                           ))))
                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_57_0~4459@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                              temp_57_1~4479@
                                                                                                                                                                                                                                            ))
                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                             (= temp_58_0~4521@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                             ))))
                                                                                                                                                                                                                                             (=>
                                                                                                                                                                                                                                              (= temp_58_1~4541@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                 )
                                                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                              ))))
                                                                                                                                                                                                                                              (and
                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                 %%location_label%%58
                                                                                                                                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_58_0~4521@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                   temp_58_1~4541@
                                                                                                                                                                                                                                               ))))
                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_58_0~4521@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                  temp_58_1~4541@
                                                                                                                                                                                                                                                ))
                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                 (= temp_59_0~4588@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                       (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                     ) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                 ))))
                                                                                                                                                                                                                                                 (=>
                                                                                                                                                                                                                                                  (= temp_59_1~4623@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                        (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                       )
                                                                                                                                                                                                                                                      ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                        (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                     )))
                                                                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                        (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                  ))))))
                                                                                                                                                                                                                                                  (and
                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                     %%location_label%%59
                                                                                                                                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_59_0~4588@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                       temp_59_1~4623@
                                                                                                                                                                                                                                                   ))))
                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_59_0~4588@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                      temp_59_1~4623@
                                                                                                                                                                                                                                                    ))
                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                     (= temp_60_0~4665@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                     ))))
                                                                                                                                                                                                                                                     (=>
                                                                                                                                                                                                                                                      (= temp_60_1~4685@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                            (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                           )
                                                                                                                                                                                                                                                          ) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                         )
                                                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                      ))
                                                                                                                                                                                                                                                      (and
                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                         %%location_label%%60
                                                                                                                                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_60_0~4665@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                           temp_60_1~4685@
                                                                                                                                                                                                                                                       ))))
                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_60_0~4665@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                          temp_60_1~4685@
                                                                                                                                                                                                                                                        ))
                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                         (= temp_61_0~4727@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                         ))))
                                                                                                                                                                                                                                                         (=>
                                                                                                                                                                                                                                                          (= temp_61_1~4747@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                               )
                                                                                                                                                                                                                                                              ) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                             )
                                                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                          ))
                                                                                                                                                                                                                                                          (and
                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                             %%location_label%%61
                                                                                                                                                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_61_0~4727@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                               temp_61_1~4747@
                                                                                                                                                                                                                                                           ))))
                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_61_0~4727@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                              temp_61_1~4747@
                                                                                                                                                                                                                                                            ))
                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                             (= temp_62_0~4794@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                   (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                 ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                             ))))
                                                                                                                                                                                                                                                             (=>
                                                                                                                                                                                                                                                              (= temp_62_1~4854@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                 )
                                                                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                                                                                                                                                                                                                    (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                     )
                                                                                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                        (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                            (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                             )
                                                                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                           )
                                                                                                                                                                                                                                                                          ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                            (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                         )))
                                                                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                       )
                                                                                                                                                                                                                                                                      ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                   )))
                                                                                                                                                                                                                                                                  ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                              ))))
                                                                                                                                                                                                                                                              (and
                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                 %%location_label%%62
                                                                                                                                                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_62_0~4794@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                   temp_62_1~4854@
                                                                                                                                                                                                                                                               ))))
                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_62_0~4794@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                  temp_62_1~4854@
                                                                                                                                                                                                                                                                ))
                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                 (= temp_63_0~4896@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                 ))))
                                                                                                                                                                                                                                                                 (=>
                                                                                                                                                                                                                                                                  (= temp_63_1~4916@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
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
                                                                                                                                                                                                                                                                     %%location_label%%63
                                                                                                                                                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_63_0~4896@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                       temp_63_1~4916@
                                                                                                                                                                                                                                                                   ))))
                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_63_0~4896@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                      temp_63_1~4916@
                                                                                                                                                                                                                                                                    ))
                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                     (= temp_64_0~4958@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                     ))))
                                                                                                                                                                                                                                                                     (=>
                                                                                                                                                                                                                                                                      (= temp_64_1~4978@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                            (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                           )
                                                                                                                                                                                                                                                                          ) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                         )
                                                                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                      ))
                                                                                                                                                                                                                                                                      (and
                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                         %%location_label%%64
                                                                                                                                                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_64_0~4958@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                           temp_64_1~4978@
                                                                                                                                                                                                                                                                       ))))
                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_64_0~4958@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                          temp_64_1~4978@
                                                                                                                                                                                                                                                                        ))
                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                         (= temp_65_0~5025@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                               (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                            )))
                                                                                                                                                                                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                         ))))
                                                                                                                                                                                                                                                                         (=>
                                                                                                                                                                                                                                                                          (= temp_65_1~5050@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                             (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                 d~8@
                                                                                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                               )
                                                                                                                                                                                                                                                                              ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                          ))))))
                                                                                                                                                                                                                                                                          (and
                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                             %%location_label%%65
                                                                                                                                                                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_65_0~5025@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                               temp_65_1~5050@
                                                                                                                                                                                                                                                                           ))))
                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_65_0~5025@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                              temp_65_1~5050@
                                                                                                                                                                                                                                                                            ))
                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                             (= temp_66_0~5092@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                             ))))
                                                                                                                                                                                                                                                                             (=>
                                                                                                                                                                                                                                                                              (= temp_66_1~5122@ (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                    (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                 )))
                                                                                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                    (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                              ))))))
                                                                                                                                                                                                                                                                              (and
                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                 %%location_label%%66
                                                                                                                                                                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_66_0~5092@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                   temp_66_1~5122@
                                                                                                                                                                                                                                                                               ))))
                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_66_0~5092@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                  temp_66_1~5122@
                                                                                                                                                                                                                                                                                ))
                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                 (= temp_67_0~5164@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                 ))))
                                                                                                                                                                                                                                                                                 (=>
                                                                                                                                                                                                                                                                                  (= temp_67_1~5184@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                     )
                                                                                                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                  ))))
                                                                                                                                                                                                                                                                                  (and
                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                     %%location_label%%67
                                                                                                                                                                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_67_0~5164@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                       temp_67_1~5184@
                                                                                                                                                                                                                                                                                   ))))
                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_67_0~5164@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                      temp_67_1~5184@
                                                                                                                                                                                                                                                                                    ))
                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                     (= temp_68_0~5226@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                     ))))
                                                                                                                                                                                                                                                                                     (=>
                                                                                                                                                                                                                                                                                      (= temp_68_1~5246@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                            (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                           )
                                                                                                                                                                                                                                                                                          ) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                         )
                                                                                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                      ))
                                                                                                                                                                                                                                                                                      (and
                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                         %%location_label%%68
                                                                                                                                                                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_68_0~5226@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                           temp_68_1~5246@
                                                                                                                                                                                                                                                                                       ))))
                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_68_0~5226@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                          temp_68_1~5246@
                                                                                                                                                                                                                                                                                        ))
                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                         (= temp_69_0~5288@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                         ))))
                                                                                                                                                                                                                                                                                         (=>
                                                                                                                                                                                                                                                                                          (= temp_69_1~5308@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                             )
                                                                                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                          ))))
                                                                                                                                                                                                                                                                                          (and
                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                             %%location_label%%69
                                                                                                                                                                                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_69_0~5288@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                               temp_69_1~5308@
                                                                                                                                                                                                                                                                                           ))))
                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_69_0~5288@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                              temp_69_1~5308@
                                                                                                                                                                                                                                                                                            ))
                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                             (= temp_70_0~5355@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                   (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                                                 ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                             ))))
                                                                                                                                                                                                                                                                                             (=>
                                                                                                                                                                                                                                                                                              (= temp_70_1~5380@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                    (Poly%main!nl_basics.Elem. d~8@)
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
                                                                                                                                                                                                                                                                                                 %%location_label%%70
                                                                                                                                                                                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_70_0~5355@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                   temp_70_1~5380@
                                                                                                                                                                                                                                                                                               ))))
                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_70_0~5355@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                  temp_70_1~5380@
                                                                                                                                                                                                                                                                                                ))
                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                 (= temp_71_0~5422@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                 ))))
                                                                                                                                                                                                                                                                                                 (=>
                                                                                                                                                                                                                                                                                                  (= temp_71_1~5442@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                     (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                       (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                         a~2@
                                                                                                                                                                                                                                                                                                  )))))))
                                                                                                                                                                                                                                                                                                  (and
                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                     %%location_label%%71
                                                                                                                                                                                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_71_0~5422@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                       temp_71_1~5442@
                                                                                                                                                                                                                                                                                                   ))))
                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_71_0~5422@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                      temp_71_1~5442@
                                                                                                                                                                                                                                                                                                    ))
                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                     (= temp_72_0~5484@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                     ))))
                                                                                                                                                                                                                                                                                                     (=>
                                                                                                                                                                                                                                                                                                      (= temp_72_1~5504@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                         )
                                                                                                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                      ))))
                                                                                                                                                                                                                                                                                                      (and
                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                         %%location_label%%72
                                                                                                                                                                                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_72_0~5484@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                           temp_72_1~5504@
                                                                                                                                                                                                                                                                                                       ))))
                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_72_0~5484@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                          temp_72_1~5504@
                                                                                                                                                                                                                                                                                                        ))
                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                         (= temp_73_0~5546@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                         ))))
                                                                                                                                                                                                                                                                                                         (=>
                                                                                                                                                                                                                                                                                                          (= temp_73_1~5566@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                               )
                                                                                                                                                                                                                                                                                                              ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                             )
                                                                                                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                          ))
                                                                                                                                                                                                                                                                                                          (and
                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                             %%location_label%%73
                                                                                                                                                                                                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_73_0~5546@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                               temp_73_1~5566@
                                                                                                                                                                                                                                                                                                           ))))
                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_73_0~5546@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                              temp_73_1~5566@
                                                                                                                                                                                                                                                                                                            ))
                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                             (= temp_74_0~5608@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                             ))))
                                                                                                                                                                                                                                                                                                             (=>
                                                                                                                                                                                                                                                                                                              (= temp_74_1~5628@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                    (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                   )
                                                                                                                                                                                                                                                                                                                  ) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                 )
                                                                                                                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                              ))
                                                                                                                                                                                                                                                                                                              (and
                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                 %%location_label%%74
                                                                                                                                                                                                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_74_0~5608@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                   temp_74_1~5628@
                                                                                                                                                                                                                                                                                                               ))))
                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_74_0~5608@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                  temp_74_1~5628@
                                                                                                                                                                                                                                                                                                                ))
                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                 (= temp_75_0~5670@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                 ))))
                                                                                                                                                                                                                                                                                                                 (=>
                                                                                                                                                                                                                                                                                                                  (= temp_75_1~5690@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                     )
                                                                                                                                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                  ))))
                                                                                                                                                                                                                                                                                                                  (and
                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                     %%location_label%%75
                                                                                                                                                                                                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_75_0~5670@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                       temp_75_1~5690@
                                                                                                                                                                                                                                                                                                                   ))))
                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_75_0~5670@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                      temp_75_1~5690@
                                                                                                                                                                                                                                                                                                                    ))
                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                     (= temp_76_0~5732@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                     ))))
                                                                                                                                                                                                                                                                                                                     (=>
                                                                                                                                                                                                                                                                                                                      (= temp_76_1~5752@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                         (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                           (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                             c~6@
                                                                                                                                                                                                                                                                                                                      )))))))
                                                                                                                                                                                                                                                                                                                      (and
                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                         %%location_label%%76
                                                                                                                                                                                                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_76_0~5732@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                           temp_76_1~5752@
                                                                                                                                                                                                                                                                                                                       ))))
                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_76_0~5732@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                          temp_76_1~5752@
                                                                                                                                                                                                                                                                                                                        ))
                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                         (= temp_77_0~5816@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                                                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                              )))
                                                                                                                                                                                                                                                                                                                             ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. (main!nl_basics.as_elem.? (I 49)))
                                                                                                                                                                                                                                                                                                                         ))))
                                                                                                                                                                                                                                                                                                                         (=>
                                                                                                                                                                                                                                                                                                                          (= temp_77_1~5858@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. (main!nl_basics.as_elem.?
                                                                                                                                                                                                                                                                                                                                (I 49)
                                                                                                                                                                                                                                                                                                                             )))
                                                                                                                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                 )
                                                                                                                                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                               )))
                                                                                                                                                                                                                                                                                                                              ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                          ))))
                                                                                                                                                                                                                                                                                                                          (and
                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                                             %%location_label%%77
                                                                                                                                                                                                                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_77_0~5816@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                               temp_77_1~5858@
                                                                                                                                                                                                                                                                                                                           ))))
                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_77_0~5816@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                              temp_77_1~5858@
                                                                                                                                                                                                                                                                                                                            ))
                                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                                             (= temp_78_0~5900@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                                                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                             ))))
                                                                                                                                                                                                                                                                                                                             (=>
                                                                                                                                                                                                                                                                                                                              (= temp_78_1~5920@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                 )
                                                                                                                                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                              ))))
                                                                                                                                                                                                                                                                                                                              (and
                                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                                 %%location_label%%78
                                                                                                                                                                                                                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_78_0~5900@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                   temp_78_1~5920@
                                                                                                                                                                                                                                                                                                                               ))))
                                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_78_0~5900@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                  temp_78_1~5920@
                                                                                                                                                                                                                                                                                                                                ))
                                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                                 (= temp_79_0~5962@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                 ))))
                                                                                                                                                                                                                                                                                                                                 (=>
                                                                                                                                                                                                                                                                                                                                  (= temp_79_1~5982@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                     )
                                                                                                                                                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                  ))))
                                                                                                                                                                                                                                                                                                                                  (and
                                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                                     %%location_label%%79
                                                                                                                                                                                                                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_79_0~5962@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                       temp_79_1~5982@
                                                                                                                                                                                                                                                                                                                                   ))))
                                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_79_0~5962@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                      temp_79_1~5982@
                                                                                                                                                                                                                                                                                                                                    ))
                                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                                     (= temp_80_0~6024@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                     ))))
                                                                                                                                                                                                                                                                                                                                     (=>
                                                                                                                                                                                                                                                                                                                                      (= temp_80_1~6044@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                            (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                           )
                                                                                                                                                                                                                                                                                                                                          ) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                         )
                                                                                                                                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                      ))
                                                                                                                                                                                                                                                                                                                                      (and
                                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                                         %%location_label%%80
                                                                                                                                                                                                                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_80_0~6024@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                           temp_80_1~6044@
                                                                                                                                                                                                                                                                                                                                       ))))
                                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_80_0~6024@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                          temp_80_1~6044@
                                                                                                                                                                                                                                                                                                                                        ))
                                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                                         (= temp_81_0~6098@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. (main!nl_basics.as_elem.? (I 85))) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                              b~4@
                                                                                                                                                                                                                                                                                                                                            ))
                                                                                                                                                                                                                                                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                               (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                         ))))))
                                                                                                                                                                                                                                                                                                                                         (=>
                                                                                                                                                                                                                                                                                                                                          (= temp_81_1~6130@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. (main!nl_basics.as_elem.?
                                                                                                                                                                                                                                                                                                                                                (I 85)
                                                                                                                                                                                                                                                                                                                                             )))
                                                                                                                                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                          ))))))
                                                                                                                                                                                                                                                                                                                                          (and
                                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                                                             %%location_label%%81
                                                                                                                                                                                                                                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_81_0~6098@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                               temp_81_1~6130@
                                                                                                                                                                                                                                                                                                                                           ))))
                                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_81_0~6098@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                              temp_81_1~6130@
                                                                                                                                                                                                                                                                                                                                            ))
                                                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                                                             (= temp_82_0~6172@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                                                                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                             ))))
                                                                                                                                                                                                                                                                                                                                             (=>
                                                                                                                                                                                                                                                                                                                                              (= temp_82_1~6192@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                 )
                                                                                                                                                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                              ))))
                                                                                                                                                                                                                                                                                                                                              (and
                                                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                                                 %%location_label%%82
                                                                                                                                                                                                                                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_82_0~6172@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                   temp_82_1~6192@
                                                                                                                                                                                                                                                                                                                                               ))))
                                                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_82_0~6172@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                  temp_82_1~6192@
                                                                                                                                                                                                                                                                                                                                                ))
                                                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                                                 (= temp_83_0~6239@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                       (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                                                                                                     ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                 ))))
                                                                                                                                                                                                                                                                                                                                                 (=>
                                                                                                                                                                                                                                                                                                                                                  (= temp_83_1~6294@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                     )
                                                                                                                                                                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                                                                                                                                                                                                                                                                                                        (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                            (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                             )
                                                                                                                                                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                           )))))
                                                                                                                                                                                                                                                                                                                                                          ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                         )
                                                                                                                                                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                       )))
                                                                                                                                                                                                                                                                                                                                                      ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                  ))))
                                                                                                                                                                                                                                                                                                                                                  (and
                                                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                                                     %%location_label%%83
                                                                                                                                                                                                                                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_83_0~6239@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                       temp_83_1~6294@
                                                                                                                                                                                                                                                                                                                                                   ))))
                                                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_83_0~6239@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                      temp_83_1~6294@
                                                                                                                                                                                                                                                                                                                                                    ))
                                                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                                                     (= temp_84_0~6343@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. (main!nl_basics.as_elem.? (I 29))) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                          c~6@
                                                                                                                                                                                                                                                                                                                                                        ))
                                                                                                                                                                                                                                                                                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                     ))))
                                                                                                                                                                                                                                                                                                                                                     (=>
                                                                                                                                                                                                                                                                                                                                                      (= temp_84_1~6370@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.as_elem.?
                                                                                                                                                                                                                                                                                                                                                              (I 29)
                                                                                                                                                                                                                                                                                                                                                             )
                                                                                                                                                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                           )
                                                                                                                                                                                                                                                                                                                                                          ) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                         )
                                                                                                                                                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                      ))
                                                                                                                                                                                                                                                                                                                                                      (and
                                                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                                                         %%location_label%%84
                                                                                                                                                                                                                                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_84_0~6343@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                           temp_84_1~6370@
                                                                                                                                                                                                                                                                                                                                                       ))))
                                                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_84_0~6343@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                          temp_84_1~6370@
                                                                                                                                                                                                                                                                                                                                                        ))
                                                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                                                         (= temp_85_0~6417@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                               (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                            )))
                                                                                                                                                                                                                                                                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                         ))))
                                                                                                                                                                                                                                                                                                                                                         (=>
                                                                                                                                                                                                                                                                                                                                                          (= temp_85_1~6467@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                                (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                    (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                        (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                       )
                                                                                                                                                                                                                                                                                                                                                                      ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                        (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                     )))
                                                                                                                                                                                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                   )
                                                                                                                                                                                                                                                                                                                                                                  ) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                 )
                                                                                                                                                                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                             )))
                                                                                                                                                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                          ))))
                                                                                                                                                                                                                                                                                                                                                          (and
                                                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                                                                             %%location_label%%85
                                                                                                                                                                                                                                                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_85_0~6417@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                               temp_85_1~6467@
                                                                                                                                                                                                                                                                                                                                                           ))))
                                                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_85_0~6417@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                              temp_85_1~6467@
                                                                                                                                                                                                                                                                                                                                                            ))
                                                                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                                                                             (= temp_86_0~6514@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                                                                                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                   (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                             ))))))
                                                                                                                                                                                                                                                                                                                                                             (=>
                                                                                                                                                                                                                                                                                                                                                              (= temp_86_1~6564@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                 )
                                                                                                                                                                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                                                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                        (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                            (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                           )
                                                                                                                                                                                                                                                                                                                                                                          ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                            (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                         )))
                                                                                                                                                                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                     )))
                                                                                                                                                                                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                              ))))))
                                                                                                                                                                                                                                                                                                                                                              (and
                                                                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                                                                 %%location_label%%86
                                                                                                                                                                                                                                                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_86_0~6514@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                   temp_86_1~6564@
                                                                                                                                                                                                                                                                                                                                                               ))))
                                                                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_86_0~6514@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                  temp_86_1~6564@
                                                                                                                                                                                                                                                                                                                                                                ))
                                                                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                                                                 (= temp_87_0~6611@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                                       (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                                                                                                                     ) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                 ))))
                                                                                                                                                                                                                                                                                                                                                                 (=>
                                                                                                                                                                                                                                                                                                                                                                  (= temp_87_1~6661@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                     )
                                                                                                                                                                                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                                        (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                               )
                                                                                                                                                                                                                                                                                                                                                                              ) (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                (Poly%main!nl_basics.Elem. b~4@)
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
                                                                                                                                                                                                                                                                                                                                                                     %%location_label%%87
                                                                                                                                                                                                                                                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_87_0~6611@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                       temp_87_1~6661@
                                                                                                                                                                                                                                                                                                                                                                   ))))
                                                                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_87_0~6611@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                      temp_87_1~6661@
                                                                                                                                                                                                                                                                                                                                                                    ))
                                                                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                                                                     (= temp_88_0~6708@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                           (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                                                                                                                         ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                           (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                        )))
                                                                                                                                                                                                                                                                                                                                                                       ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                     ))
                                                                                                                                                                                                                                                                                                                                                                     (=>
                                                                                                                                                                                                                                                                                                                                                                      (= temp_88_1~6733@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                            (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                         )))))
                                                                                                                                                                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                      ))
                                                                                                                                                                                                                                                                                                                                                                      (and
                                                                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                                                                         %%location_label%%88
                                                                                                                                                                                                                                                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_88_0~6708@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                           temp_88_1~6733@
                                                                                                                                                                                                                                                                                                                                                                       ))))
                                                                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_88_0~6708@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                          temp_88_1~6733@
                                                                                                                                                                                                                                                                                                                                                                        ))
                                                                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                                                                         (= temp_89_0~6780@ (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                                                                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                               (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                                                                                                                                             ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                         ))))
                                                                                                                                                                                                                                                                                                                                                                         (=>
                                                                                                                                                                                                                                                                                                                                                                          (= temp_89_1~6805@ (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                             )
                                                                                                                                                                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                               )
                                                                                                                                                                                                                                                                                                                                                                              ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                          ))))
                                                                                                                                                                                                                                                                                                                                                                          (and
                                                                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                                                                                             %%location_label%%89
                                                                                                                                                                                                                                                                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_89_0~6780@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                               temp_89_1~6805@
                                                                                                                                                                                                                                                                                                                                                                           ))))
                                                                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_89_0~6780@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                              temp_89_1~6805@
                                                                                                                                                                                                                                                                                                                                                                            ))
                                                                                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                                                                                             (= temp_90_0~6852@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                                                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                   (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                                                                                                                                 ) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                                                                                                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                             ))))
                                                                                                                                                                                                                                                                                                                                                                             (=>
                                                                                                                                                                                                                                                                                                                                                                              (= temp_90_1~6902@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                                                                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                            (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                           )
                                                                                                                                                                                                                                                                                                                                                                                          ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                            (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                         )))
                                                                                                                                                                                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                       )
                                                                                                                                                                                                                                                                                                                                                                                      ) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                     )
                                                                                                                                                                                                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                   )
                                                                                                                                                                                                                                                                                                                                                                                  ) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                 )
                                                                                                                                                                                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                              ))))
                                                                                                                                                                                                                                                                                                                                                                              (and
                                                                                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                                                                                 %%location_label%%90
                                                                                                                                                                                                                                                                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_90_0~6852@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                   temp_90_1~6902@
                                                                                                                                                                                                                                                                                                                                                                               ))))
                                                                                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_90_0~6852@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                  temp_90_1~6902@
                                                                                                                                                                                                                                                                                                                                                                                ))
                                                                                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                                                                                 (= temp_91_0~6944@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                                                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                 ))))
                                                                                                                                                                                                                                                                                                                                                                                 (=>
                                                                                                                                                                                                                                                                                                                                                                                  (= temp_91_1~6964@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                     )
                                                                                                                                                                                                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                  ))))
                                                                                                                                                                                                                                                                                                                                                                                  (and
                                                                                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                                                                                     %%location_label%%91
                                                                                                                                                                                                                                                                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_91_0~6944@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                       temp_91_1~6964@
                                                                                                                                                                                                                                                                                                                                                                                   ))))
                                                                                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_91_0~6944@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                      temp_91_1~6964@
                                                                                                                                                                                                                                                                                                                                                                                    ))
                                                                                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                                                                                     (= temp_92_0~7006@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                                                                                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                                                                                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                     ))))
                                                                                                                                                                                                                                                                                                                                                                                     (=>
                                                                                                                                                                                                                                                                                                                                                                                      (= temp_92_1~7026@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                         )
                                                                                                                                                                                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                      ))))
                                                                                                                                                                                                                                                                                                                                                                                      (and
                                                                                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                                                                                         %%location_label%%92
                                                                                                                                                                                                                                                                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_92_0~7006@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                           temp_92_1~7026@
                                                                                                                                                                                                                                                                                                                                                                                       ))))
                                                                                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_92_0~7006@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                          temp_92_1~7026@
                                                                                                                                                                                                                                                                                                                                                                                        ))
                                                                                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                                                                                         (= temp_93_0~7073@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                                                                                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                               (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                                                                                                                                                             ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                               (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                            )))
                                                                                                                                                                                                                                                                                                                                                                                           ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                         ))
                                                                                                                                                                                                                                                                                                                                                                                         (=>
                                                                                                                                                                                                                                                                                                                                                                                          (= temp_93_1~7098@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                                                                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                                (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                               )
                                                                                                                                                                                                                                                                                                                                                                                              ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                                (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                             )))
                                                                                                                                                                                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                          ))
                                                                                                                                                                                                                                                                                                                                                                                          (and
                                                                                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                                                                                                             %%location_label%%93
                                                                                                                                                                                                                                                                                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_93_0~7073@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                               temp_93_1~7098@
                                                                                                                                                                                                                                                                                                                                                                                           ))))
                                                                                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_93_0~7073@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                              temp_93_1~7098@
                                                                                                                                                                                                                                                                                                                                                                                            ))
                                                                                                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                                                                                                             (= temp_94_0~7145@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                   (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                                                                                                                                                 ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                                                                                                                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                             ))))
                                                                                                                                                                                                                                                                                                                                                                                             (=>
                                                                                                                                                                                                                                                                                                                                                                                              (= temp_94_1~7170@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                    (Poly%main!nl_basics.Elem. c~6@)
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
                                                                                                                                                                                                                                                                                                                                                                                                 %%location_label%%94
                                                                                                                                                                                                                                                                                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_94_0~7145@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                   temp_94_1~7170@
                                                                                                                                                                                                                                                                                                                                                                                               ))))
                                                                                                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_94_0~7145@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                  temp_94_1~7170@
                                                                                                                                                                                                                                                                                                                                                                                                ))
                                                                                                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                                                                                                 (= temp_95_0~7212@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                                                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                                                                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                 ))))
                                                                                                                                                                                                                                                                                                                                                                                                 (=>
                                                                                                                                                                                                                                                                                                                                                                                                  (= temp_95_1~7232@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                     )
                                                                                                                                                                                                                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                  ))))
                                                                                                                                                                                                                                                                                                                                                                                                  (and
                                                                                                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                                                                                                     %%location_label%%95
                                                                                                                                                                                                                                                                                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_95_0~7212@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                       temp_95_1~7232@
                                                                                                                                                                                                                                                                                                                                                                                                   ))))
                                                                                                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_95_0~7212@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                      temp_95_1~7232@
                                                                                                                                                                                                                                                                                                                                                                                                    ))
                                                                                                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                                                                                                     (= temp_96_0~7279@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                                                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                                                                                                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                           (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                                                                                                                                                         ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                     ))))
                                                                                                                                                                                                                                                                                                                                                                                                     (=>
                                                                                                                                                                                                                                                                                                                                                                                                      (= temp_96_1~7319@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                                                                            (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                             )
                                                                                                                                                                                                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                         )))
                                                                                                                                                                                                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                             )
                                                                                                                                                                                                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                      ))))))
                                                                                                                                                                                                                                                                                                                                                                                                      (and
                                                                                                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                                                                                                         %%location_label%%96
                                                                                                                                                                                                                                                                                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_96_0~7279@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                           temp_96_1~7319@
                                                                                                                                                                                                                                                                                                                                                                                                       ))))
                                                                                                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_96_0~7279@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                          temp_96_1~7319@
                                                                                                                                                                                                                                                                                                                                                                                                        ))
                                                                                                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                                                                                                         (= temp_97_0~7361@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                                                                                                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                         ))))
                                                                                                                                                                                                                                                                                                                                                                                                         (=>
                                                                                                                                                                                                                                                                                                                                                                                                          (= temp_97_1~7381@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                                (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                               )
                                                                                                                                                                                                                                                                                                                                                                                                              ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                             )
                                                                                                                                                                                                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                          ))
                                                                                                                                                                                                                                                                                                                                                                                                          (and
                                                                                                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                                                                                                                             %%location_label%%97
                                                                                                                                                                                                                                                                                                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_97_0~7361@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                               temp_97_1~7381@
                                                                                                                                                                                                                                                                                                                                                                                                           ))))
                                                                                                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_97_0~7361@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                              temp_97_1~7381@
                                                                                                                                                                                                                                                                                                                                                                                                            ))
                                                                                                                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                                                                                                                             (= temp_98_0~7423@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                                                                                                                                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                             ))))
                                                                                                                                                                                                                                                                                                                                                                                                             (=>
                                                                                                                                                                                                                                                                                                                                                                                                              (= temp_98_1~7443@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                                                 )
                                                                                                                                                                                                                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                              ))))
                                                                                                                                                                                                                                                                                                                                                                                                              (and
                                                                                                                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                                                                                                                 %%location_label%%98
                                                                                                                                                                                                                                                                                                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_98_0~7423@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                   temp_98_1~7443@
                                                                                                                                                                                                                                                                                                                                                                                                               ))))
                                                                                                                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_98_0~7423@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                  temp_98_1~7443@
                                                                                                                                                                                                                                                                                                                                                                                                                ))
                                                                                                                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                                                                                                                 (= temp_99_0~7490@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                                       (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                                                                                                                                                                     ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                                       (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                                    )))
                                                                                                                                                                                                                                                                                                                                                                                                                   ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                                 ))
                                                                                                                                                                                                                                                                                                                                                                                                                 (=>
                                                                                                                                                                                                                                                                                                                                                                                                                  (= temp_99_1~7545@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                                                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                                         )
                                                                                                                                                                                                                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                                       )))
                                                                                                                                                                                                                                                                                                                                                                                                                      ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                                             )
                                                                                                                                                                                                                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                                           )))
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
                                                                                                                                                                                                                                                                                                                                                                                                                     %%location_label%%99
                                                                                                                                                                                                                                                                                                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_99_0~7490@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                       temp_99_1~7545@
                                                                                                                                                                                                                                                                                                                                                                                                                   ))))
                                                                                                                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_99_0~7490@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                      temp_99_1~7545@
                                                                                                                                                                                                                                                                                                                                                                                                                    ))
                                                                                                                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                                                                                                                     (= temp_100_0~7587@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                                                                                                                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                                     ))))
                                                                                                                                                                                                                                                                                                                                                                                                                     (=>
                                                                                                                                                                                                                                                                                                                                                                                                                      (= temp_100_1~7607@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                                         )
                                                                                                                                                                                                                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                                      ))))
                                                                                                                                                                                                                                                                                                                                                                                                                      (and
                                                                                                                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                                                                                                                         %%location_label%%100
                                                                                                                                                                                                                                                                                                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_100_0~7587@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                           temp_100_1~7607@
                                                                                                                                                                                                                                                                                                                                                                                                                       ))))
                                                                                                                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_100_0~7587@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                          temp_100_1~7607@
                                                                                                                                                                                                                                                                                                                                                                                                                        ))
                                                                                                                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                                                                                                                         (= temp_101_0~7654@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                                                                                                                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                                               (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                                         ))))))
                                                                                                                                                                                                                                                                                                                                                                                                                         (=>
                                                                                                                                                                                                                                                                                                                                                                                                                          (= temp_101_1~7704@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                                             )
                                                                                                                                                                                                                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                                                                                                                                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                                                    (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                                                                                                                                                                                                                                                                                                                                        (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                                                       )
                                                                                                                                                                                                                                                                                                                                                                                                                                      ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                                                        (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                                                     )))
                                                                                                                                                                                                                                                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                                                 )))
                                                                                                                                                                                                                                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                                          ))))))
                                                                                                                                                                                                                                                                                                                                                                                                                          (and
                                                                                                                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                                                                                                                                             %%location_label%%101
                                                                                                                                                                                                                                                                                                                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_101_0~7654@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                               temp_101_1~7704@
                                                                                                                                                                                                                                                                                                                                                                                                                           ))))
                                                                                                                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_101_0~7654@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                              temp_101_1~7704@
                                                                                                                                                                                                                                                                                                                                                                                                                            ))
                                                                                                                                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                                                                                                                                             (= temp_102_0~7753@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. (main!nl_basics.as_elem.? (I 99))) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                                  b~4@
                                                                                                                                                                                                                                                                                                                                                                                                                                ))
                                                                                                                                                                                                                                                                                                                                                                                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                                             ))))
                                                                                                                                                                                                                                                                                                                                                                                                                             (=>
                                                                                                                                                                                                                                                                                                                                                                                                                              (= temp_102_1~7780@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                                                 )
                                                                                                                                                                                                                                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.as_elem.?
                                                                                                                                                                                                                                                                                                                                                                                                                                    (I 99)
                                                                                                                                                                                                                                                                                                                                                                                                                                   )
                                                                                                                                                                                                                                                                                                                                                                                                                                  ) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                                                              ))))
                                                                                                                                                                                                                                                                                                                                                                                                                              (and
                                                                                                                                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                 %%location_label%%102
                                                                                                                                                                                                                                                                                                                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_102_0~7753@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                                   temp_102_1~7780@
                                                                                                                                                                                                                                                                                                                                                                                                                               ))))
                                                                                                                                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_102_0~7753@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                                  temp_102_1~7780@
                                                                                                                                                                                                                                                                                                                                                                                                                                ))
                                                                                                                                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                 (= temp_103_0~7827@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                                                                                                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                                                       (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                                                                                                                                                                                     ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                                                 ))))
                                                                                                                                                                                                                                                                                                                                                                                                                                 (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                  (= temp_103_1~7889@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                                                     )
                                                                                                                                                                                                                                                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                                                                                                                                                                                                                                                                                                                                                                                        (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                                                         )
                                                                                                                                                                                                                                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                                                            (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.as_elem.?
                                                                                                                                                                                                                                                                                                                                                                                                                                                (I 4)
                                                                                                                                                                                                                                                                                                                                                                                                                                               )
                                                                                                                                                                                                                                                                                                                                                                                                                                              ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                                                             )))
                                                                                                                                                                                                                                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                                                           )))
                                                                                                                                                                                                                                                                                                                                                                                                                                          ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                                                       )))
                                                                                                                                                                                                                                                                                                                                                                                                                                      ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                                                  ))))
                                                                                                                                                                                                                                                                                                                                                                                                                                  (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                   (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                    %%location_label%%103
                                                                                                                                                                                                                                                                                                                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_103_0~7827@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                                      temp_103_1~7889@
 )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
 (get-info :version)
 (assert
  %%query%%
 )
 (set-option :rlimit 4294967295)
 (check-sat)
