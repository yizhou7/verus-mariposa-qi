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
;; mariposa_data/uf//5735182439495464284/nlqi_verus/src/main.rs:7:1: 7:65 (#0)
(push)
 (declare-const a~2@ main!nl_basics.Elem.)
 (declare-const b~4@ main!nl_basics.Elem.)
 (declare-const c~6@ main!nl_basics.Elem.)
 (declare-const d~8@ main!nl_basics.Elem.)
 (declare-const m~10@ main!nl_basics.Elem.)
 (declare-const temp_0_0~35@ main!nl_basics.Elem.)
 (declare-const temp_0_1~75@ main!nl_basics.Elem.)
 (declare-const temp_1_0~122@ main!nl_basics.Elem.)
 (declare-const temp_1_1~147@ main!nl_basics.Elem.)
 (declare-const temp_2_0~199@ main!nl_basics.Elem.)
 (declare-const temp_2_1~259@ main!nl_basics.Elem.)
 (declare-const temp_3_0~301@ main!nl_basics.Elem.)
 (declare-const temp_3_1~331@ main!nl_basics.Elem.)
 (declare-const temp_4_0~373@ main!nl_basics.Elem.)
 (declare-const temp_4_1~393@ main!nl_basics.Elem.)
 (declare-const temp_5_0~435@ main!nl_basics.Elem.)
 (declare-const temp_5_1~455@ main!nl_basics.Elem.)
 (declare-const temp_6_0~497@ main!nl_basics.Elem.)
 (declare-const temp_6_1~517@ main!nl_basics.Elem.)
 (declare-const temp_7_0~564@ main!nl_basics.Elem.)
 (declare-const temp_7_1~619@ main!nl_basics.Elem.)
 (declare-const temp_8_0~666@ main!nl_basics.Elem.)
 (declare-const temp_8_1~716@ main!nl_basics.Elem.)
 (declare-const temp_9_0~758@ main!nl_basics.Elem.)
 (declare-const temp_9_1~778@ main!nl_basics.Elem.)
 (declare-const temp_10_0~820@ main!nl_basics.Elem.)
 (declare-const temp_10_1~840@ main!nl_basics.Elem.)
 (declare-const temp_11_0~892@ main!nl_basics.Elem.)
 (declare-const temp_11_1~952@ main!nl_basics.Elem.)
 (declare-const temp_12_0~994@ main!nl_basics.Elem.)
 (declare-const temp_12_1~1014@ main!nl_basics.Elem.)
 (declare-const temp_13_0~1056@ main!nl_basics.Elem.)
 (declare-const temp_13_1~1076@ main!nl_basics.Elem.)
 (declare-const temp_14_0~1123@ main!nl_basics.Elem.)
 (declare-const temp_14_1~1148@ main!nl_basics.Elem.)
 (declare-const temp_15_0~1197@ main!nl_basics.Elem.)
 (declare-const temp_15_1~1224@ main!nl_basics.Elem.)
 (declare-const temp_16_0~1271@ main!nl_basics.Elem.)
 (declare-const temp_16_1~1296@ main!nl_basics.Elem.)
 (declare-const temp_17_0~1343@ main!nl_basics.Elem.)
 (declare-const temp_17_1~1393@ main!nl_basics.Elem.)
 (declare-const temp_18_0~1440@ main!nl_basics.Elem.)
 (declare-const temp_18_1~1495@ main!nl_basics.Elem.)
 (declare-const temp_19_0~1542@ main!nl_basics.Elem.)
 (declare-const temp_19_1~1567@ main!nl_basics.Elem.)
 (declare-const temp_20_0~1619@ main!nl_basics.Elem.)
 (declare-const temp_20_1~1649@ main!nl_basics.Elem.)
 (declare-const temp_21_0~1691@ main!nl_basics.Elem.)
 (declare-const temp_21_1~1711@ main!nl_basics.Elem.)
 (declare-const temp_22_0~1758@ main!nl_basics.Elem.)
 (declare-const temp_22_1~1808@ main!nl_basics.Elem.)
 (declare-const temp_23_0~1850@ main!nl_basics.Elem.)
 (declare-const temp_23_1~1870@ main!nl_basics.Elem.)
 (declare-const temp_24_0~1912@ main!nl_basics.Elem.)
 (declare-const temp_24_1~1932@ main!nl_basics.Elem.)
 (declare-const temp_25_0~1974@ main!nl_basics.Elem.)
 (declare-const temp_25_1~1994@ main!nl_basics.Elem.)
 (declare-const temp_26_0~2046@ main!nl_basics.Elem.)
 (declare-const temp_26_1~2076@ main!nl_basics.Elem.)
 (declare-const temp_27_0~2123@ main!nl_basics.Elem.)
 (declare-const temp_27_1~2148@ main!nl_basics.Elem.)
 (declare-const temp_28_0~2200@ main!nl_basics.Elem.)
 (declare-const temp_28_1~2230@ main!nl_basics.Elem.)
 (declare-const temp_29_0~2277@ main!nl_basics.Elem.)
 (declare-const temp_29_1~2302@ main!nl_basics.Elem.)
 (declare-const temp_30_0~2344@ main!nl_basics.Elem.)
 (declare-const temp_30_1~2364@ main!nl_basics.Elem.)
 (declare-const temp_31_0~2411@ main!nl_basics.Elem.)
 (declare-const temp_31_1~2436@ main!nl_basics.Elem.)
 (declare-const temp_32_0~2478@ main!nl_basics.Elem.)
 (declare-const temp_32_1~2498@ main!nl_basics.Elem.)
 (declare-const temp_33_0~2540@ main!nl_basics.Elem.)
 (declare-const temp_33_1~2570@ main!nl_basics.Elem.)
 (declare-const temp_34_0~2612@ main!nl_basics.Elem.)
 (declare-const temp_34_1~2642@ main!nl_basics.Elem.)
 (declare-const temp_35_0~2689@ main!nl_basics.Elem.)
 (declare-const temp_35_1~2714@ main!nl_basics.Elem.)
 (declare-const temp_36_0~2751@ main!nl_basics.Elem.)
 (declare-const temp_36_1~2766@ main!nl_basics.Elem.)
 (declare-const temp_37_0~2808@ main!nl_basics.Elem.)
 (declare-const temp_37_1~2828@ main!nl_basics.Elem.)
 (declare-const temp_38_0~2875@ main!nl_basics.Elem.)
 (declare-const temp_38_1~2900@ main!nl_basics.Elem.)
 (declare-const temp_39_0~2952@ main!nl_basics.Elem.)
 (declare-const temp_39_1~2982@ main!nl_basics.Elem.)
 (declare-const temp_40_0~3024@ main!nl_basics.Elem.)
 (declare-const temp_40_1~3044@ main!nl_basics.Elem.)
 (declare-const temp_41_0~3096@ main!nl_basics.Elem.)
 (declare-const temp_41_1~3121@ main!nl_basics.Elem.)
 (declare-const temp_42_0~3178@ main!nl_basics.Elem.)
 (declare-const temp_42_1~3213@ main!nl_basics.Elem.)
 (declare-const temp_43_0~3272@ main!nl_basics.Elem.)
 (declare-const temp_43_1~3309@ main!nl_basics.Elem.)
 (declare-const temp_44_0~3351@ main!nl_basics.Elem.)
 (declare-const temp_44_1~3371@ main!nl_basics.Elem.)
 (declare-const temp_45_0~3418@ main!nl_basics.Elem.)
 (declare-const temp_45_1~3443@ main!nl_basics.Elem.)
 (declare-const temp_46_0~3485@ main!nl_basics.Elem.)
 (declare-const temp_46_1~3505@ main!nl_basics.Elem.)
 (declare-const temp_47_0~3552@ main!nl_basics.Elem.)
 (declare-const temp_47_1~3607@ main!nl_basics.Elem.)
 (declare-const temp_48_0~3649@ main!nl_basics.Elem.)
 (declare-const temp_48_1~3669@ main!nl_basics.Elem.)
 (declare-const temp_49_0~3711@ main!nl_basics.Elem.)
 (declare-const temp_49_1~3731@ main!nl_basics.Elem.)
 (declare-const temp_50_0~3778@ main!nl_basics.Elem.)
 (declare-const temp_50_1~3803@ main!nl_basics.Elem.)
 (declare-const temp_51_0~3845@ main!nl_basics.Elem.)
 (declare-const temp_51_1~3875@ main!nl_basics.Elem.)
 (declare-const temp_52_0~3917@ main!nl_basics.Elem.)
 (declare-const temp_52_1~3937@ main!nl_basics.Elem.)
 (declare-const temp_53_0~3984@ main!nl_basics.Elem.)
 (declare-const temp_53_1~4019@ main!nl_basics.Elem.)
 (declare-const temp_54_0~4061@ main!nl_basics.Elem.)
 (declare-const temp_54_1~4081@ main!nl_basics.Elem.)
 (declare-const temp_55_0~4118@ main!nl_basics.Elem.)
 (declare-const temp_55_1~4133@ main!nl_basics.Elem.)
 (declare-const temp_56_0~4175@ main!nl_basics.Elem.)
 (declare-const temp_56_1~4195@ main!nl_basics.Elem.)
 (declare-const temp_57_0~4237@ main!nl_basics.Elem.)
 (declare-const temp_57_1~4257@ main!nl_basics.Elem.)
 (declare-const temp_58_0~4304@ main!nl_basics.Elem.)
 (declare-const temp_58_1~4329@ main!nl_basics.Elem.)
 (declare-const temp_59_0~4371@ main!nl_basics.Elem.)
 (declare-const temp_59_1~4391@ main!nl_basics.Elem.)
 (declare-const temp_60_0~4433@ main!nl_basics.Elem.)
 (declare-const temp_60_1~4453@ main!nl_basics.Elem.)
 (declare-const temp_61_0~4500@ main!nl_basics.Elem.)
 (declare-const temp_61_1~4562@ main!nl_basics.Elem.)
 (declare-const temp_62_0~4604@ main!nl_basics.Elem.)
 (declare-const temp_62_1~4624@ main!nl_basics.Elem.)
 (declare-const temp_63_0~4676@ main!nl_basics.Elem.)
 (declare-const temp_63_1~4706@ main!nl_basics.Elem.)
 (declare-const temp_64_0~4758@ main!nl_basics.Elem.)
 (declare-const temp_64_1~4788@ main!nl_basics.Elem.)
 (declare-const temp_65_0~4837@ main!nl_basics.Elem.)
 (declare-const temp_65_1~4864@ main!nl_basics.Elem.)
 (declare-const temp_66_0~4918@ main!nl_basics.Elem.)
 (declare-const temp_66_1~4980@ main!nl_basics.Elem.)
 (declare-const temp_67_0~5022@ main!nl_basics.Elem.)
 (declare-const temp_67_1~5042@ main!nl_basics.Elem.)
 (declare-const temp_68_0~5084@ main!nl_basics.Elem.)
 (declare-const temp_68_1~5104@ main!nl_basics.Elem.)
 (declare-const temp_69_0~5146@ main!nl_basics.Elem.)
 (declare-const temp_69_1~5166@ main!nl_basics.Elem.)
 (declare-const temp_70_0~5208@ main!nl_basics.Elem.)
 (declare-const temp_70_1~5228@ main!nl_basics.Elem.)
 (declare-const temp_71_0~5270@ main!nl_basics.Elem.)
 (declare-const temp_71_1~5290@ main!nl_basics.Elem.)
 (declare-const temp_72_0~5332@ main!nl_basics.Elem.)
 (declare-const temp_72_1~5352@ main!nl_basics.Elem.)
 (declare-const temp_73_0~5399@ main!nl_basics.Elem.)
 (declare-const temp_73_1~5449@ main!nl_basics.Elem.)
 (declare-const temp_74_0~5496@ main!nl_basics.Elem.)
 (declare-const temp_74_1~5521@ main!nl_basics.Elem.)
 (declare-const temp_75_0~5568@ main!nl_basics.Elem.)
 (declare-const temp_75_1~5623@ main!nl_basics.Elem.)
 (declare-const temp_76_0~5665@ main!nl_basics.Elem.)
 (declare-const temp_76_1~5685@ main!nl_basics.Elem.)
 (declare-const temp_77_0~5732@ main!nl_basics.Elem.)
 (declare-const temp_77_1~5792@ main!nl_basics.Elem.)
 (declare-const temp_78_0~5834@ main!nl_basics.Elem.)
 (declare-const temp_78_1~5854@ main!nl_basics.Elem.)
 (declare-const temp_79_0~5908@ main!nl_basics.Elem.)
 (declare-const temp_79_1~5940@ main!nl_basics.Elem.)
 (declare-const temp_80_0~5989@ main!nl_basics.Elem.)
 (declare-const temp_80_1~6016@ main!nl_basics.Elem.)
 (declare-const temp_81_0~6058@ main!nl_basics.Elem.)
 (declare-const temp_81_1~6078@ main!nl_basics.Elem.)
 (declare-const temp_82_0~6125@ main!nl_basics.Elem.)
 (declare-const temp_82_1~6150@ main!nl_basics.Elem.)
 (declare-const temp_83_0~6192@ main!nl_basics.Elem.)
 (declare-const temp_83_1~6222@ main!nl_basics.Elem.)
 (declare-const temp_84_0~6279@ main!nl_basics.Elem.)
 (declare-const temp_84_1~6314@ main!nl_basics.Elem.)
 (declare-const temp_85_0~6356@ main!nl_basics.Elem.)
 (declare-const temp_85_1~6376@ main!nl_basics.Elem.)
 (declare-const temp_86_0~6430@ main!nl_basics.Elem.)
 (declare-const temp_86_1~6492@ main!nl_basics.Elem.)
 (declare-const temp_87_0~6534@ main!nl_basics.Elem.)
 (declare-const temp_87_1~6554@ main!nl_basics.Elem.)
 (declare-const temp_88_0~6596@ main!nl_basics.Elem.)
 (declare-const temp_88_1~6616@ main!nl_basics.Elem.)
 (declare-const temp_89_0~6658@ main!nl_basics.Elem.)
 (declare-const temp_89_1~6678@ main!nl_basics.Elem.)
 (declare-const temp_90_0~6710@ main!nl_basics.Elem.)
 (declare-const temp_90_1~6720@ main!nl_basics.Elem.)
 (declare-const temp_91_0~6762@ main!nl_basics.Elem.)
 (declare-const temp_91_1~6782@ main!nl_basics.Elem.)
 (declare-const temp_92_0~6834@ main!nl_basics.Elem.)
 (declare-const temp_92_1~6864@ main!nl_basics.Elem.)
 (declare-const temp_93_0~6911@ main!nl_basics.Elem.)
 (declare-const temp_93_1~6941@ main!nl_basics.Elem.)
 (declare-const temp_94_0~6993@ main!nl_basics.Elem.)
 (declare-const temp_94_1~7023@ main!nl_basics.Elem.)
 (declare-const temp_95_0~7070@ main!nl_basics.Elem.)
 (declare-const temp_95_1~7120@ main!nl_basics.Elem.)
 (declare-const temp_96_0~7162@ main!nl_basics.Elem.)
 (declare-const temp_96_1~7182@ main!nl_basics.Elem.)
 (declare-const temp_97_0~7224@ main!nl_basics.Elem.)
 (declare-const temp_97_1~7244@ main!nl_basics.Elem.)
 (declare-const temp_98_0~7286@ main!nl_basics.Elem.)
 (declare-const temp_98_1~7306@ main!nl_basics.Elem.)
 (declare-const temp_99_0~7348@ main!nl_basics.Elem.)
 (declare-const temp_99_1~7368@ main!nl_basics.Elem.)
 (declare-const temp_100_0~7410@ main!nl_basics.Elem.)
 (declare-const temp_100_1~7430@ main!nl_basics.Elem.)
 (declare-const temp_101_0~7482@ main!nl_basics.Elem.)
 (declare-const temp_101_1~7512@ main!nl_basics.Elem.)
 (declare-const temp_102_0~7559@ main!nl_basics.Elem.)
 (declare-const temp_102_1~7584@ main!nl_basics.Elem.)
 (declare-const temp_103_0~7626@ main!nl_basics.Elem.)
 (declare-const temp_103_1~7646@ main!nl_basics.Elem.)
 (declare-const temp_104_0~7698@ main!nl_basics.Elem.)
 (declare-const temp_104_1~7728@ main!nl_basics.Elem.)
 (declare-const temp_105_0~7765@ main!nl_basics.Elem.)
 (declare-const temp_105_1~7780@ main!nl_basics.Elem.)
 (declare-const temp_106_0~7822@ main!nl_basics.Elem.)
 (declare-const temp_106_1~7842@ main!nl_basics.Elem.)
 (declare-const temp_107_0~7889@ main!nl_basics.Elem.)
 (declare-const temp_107_1~7914@ main!nl_basics.Elem.)
 (declare-const temp_108_0~7961@ main!nl_basics.Elem.)
 (declare-const temp_108_1~7986@ main!nl_basics.Elem.)
 (declare-const temp_109_0~8033@ main!nl_basics.Elem.)
 (declare-const temp_109_1~8068@ main!nl_basics.Elem.)
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
     (= temp_0_0~35@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
         (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. d~8@)
        )
       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
         (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. d~8@)
           (Poly%main!nl_basics.Elem. m~10@)
     ))))))
     (=>
      (= temp_0_1~75@ (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
          (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
            (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
              (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. m~10@)
         )))))
        ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
          (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
            (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. d~8@)
              (Poly%main!nl_basics.Elem. m~10@)
      ))))))))
      (and
       (=>
        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
        (=>
         %%location_label%%0
         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_0_0~35@) (Poly%main!nl_basics.Elem.
           temp_0_1~75@
       ))))
       (=>
        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_0_0~35@) (Poly%main!nl_basics.Elem.
          temp_0_1~75@
        ))
        (=>
         (= temp_1_0~122@ (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
             (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. d~8@)
            )
           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
             (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. d~8@)
               (Poly%main!nl_basics.Elem. m~10@)
         ))))))
         (=>
          (= temp_1_1~147@ (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
              (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. m~10@)
             )))
            ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
              (Poly%main!nl_basics.Elem. d~8@)
          ))))
          (and
           (=>
            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
            (=>
             %%location_label%%1
             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_1_0~122@) (Poly%main!nl_basics.Elem.
               temp_1_1~147@
           ))))
           (=>
            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_1_0~122@) (Poly%main!nl_basics.Elem.
              temp_1_1~147@
            ))
            (=>
             (= temp_2_0~199@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                 (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                   (Poly%main!nl_basics.Elem. d~8@)
                  )
                 ) (Poly%main!nl_basics.Elem. m~10@)
                )
               ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                   (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. m~10@)
                  )
                 ) (Poly%main!nl_basics.Elem. b~4@)
             ))))
             (=>
              (= temp_2_1~259@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                  (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                      (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                          (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. a~2@)
                            (Poly%main!nl_basics.Elem. m~10@)
                           )
                          ) (Poly%main!nl_basics.Elem. a~2@)
                         )
                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. c~6@)
                          (Poly%main!nl_basics.Elem. d~8@)
                       )))
                      ) (Poly%main!nl_basics.Elem. m~10@)
                     )
                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                      (Poly%main!nl_basics.Elem. d~8@)
                   )))
                  ) (Poly%main!nl_basics.Elem. m~10@)
                 )
                ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                    (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. m~10@)
                   )
                  ) (Poly%main!nl_basics.Elem. b~4@)
              ))))
              (and
               (=>
                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                (=>
                 %%location_label%%2
                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_2_0~199@) (Poly%main!nl_basics.Elem.
                   temp_2_1~259@
               ))))
               (=>
                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_2_0~199@) (Poly%main!nl_basics.Elem.
                  temp_2_1~259@
                ))
                (=>
                 (= temp_3_0~301@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                     (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. a~2@)
                    )
                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. c~6@)
                     (Poly%main!nl_basics.Elem. a~2@)
                 ))))
                 (=>
                  (= temp_3_1~331@ (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                      (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                        (Poly%main!nl_basics.Elem. a~2@)
                       )
                      ) (Poly%main!nl_basics.Elem. c~6@)
                     )
                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                        (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. a~2@)
                       )
                      ) (Poly%main!nl_basics.Elem. a~2@)
                  ))))
                  (and
                   (=>
                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                    (=>
                     %%location_label%%3
                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_3_0~301@) (Poly%main!nl_basics.Elem.
                       temp_3_1~331@
                   ))))
                   (=>
                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_3_0~301@) (Poly%main!nl_basics.Elem.
                      temp_3_1~331@
                    ))
                    (=>
                     (= temp_4_0~373@ (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                         (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. d~8@)
                        )
                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                         (Poly%main!nl_basics.Elem. b~4@)
                     ))))
                     (=>
                      (= temp_4_1~393@ (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                          (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. d~8@)
                         )
                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                          (Poly%main!nl_basics.Elem. b~4@)
                      ))))
                      (and
                       (=>
                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                        (=>
                         %%location_label%%4
                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_4_0~373@) (Poly%main!nl_basics.Elem.
                           temp_4_1~393@
                       ))))
                       (=>
                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_4_0~373@) (Poly%main!nl_basics.Elem.
                          temp_4_1~393@
                        ))
                        (=>
                         (= temp_5_0~435@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                             (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. b~4@)
                            )
                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. c~6@)
                             (Poly%main!nl_basics.Elem. c~6@)
                         ))))
                         (=>
                          (= temp_5_1~455@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem.
                             (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem.
                               (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem.
                                 c~6@
                          )))))))
                          (and
                           (=>
                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                            (=>
                             %%location_label%%5
                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_5_0~435@) (Poly%main!nl_basics.Elem.
                               temp_5_1~455@
                           ))))
                           (=>
                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_5_0~435@) (Poly%main!nl_basics.Elem.
                              temp_5_1~455@
                            ))
                            (=>
                             (= temp_6_0~497@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                 (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. d~8@)
                                )
                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                 (Poly%main!nl_basics.Elem. c~6@)
                             ))))
                             (=>
                              (= temp_6_1~517@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                  (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. a~2@)
                                 )
                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                  (Poly%main!nl_basics.Elem. c~6@)
                              ))))
                              (and
                               (=>
                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                (=>
                                 %%location_label%%6
                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_6_0~497@) (Poly%main!nl_basics.Elem.
                                   temp_6_1~517@
                               ))))
                               (=>
                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_6_0~497@) (Poly%main!nl_basics.Elem.
                                  temp_6_1~517@
                                ))
                                (=>
                                 (= temp_7_0~564@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                     (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. d~8@)
                                    )
                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                       (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. b~4@)
                                      )
                                     ) (Poly%main!nl_basics.Elem. m~10@)
                                 ))))
                                 (=>
                                  (= temp_7_1~619@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                      (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. d~8@)
                                     )
                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                        (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                            (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. b~4@)
                                               )
                                              ) (Poly%main!nl_basics.Elem. m~10@)
                                             )
                                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                              (Poly%main!nl_basics.Elem. d~8@)
                                           )))
                                          ) (Poly%main!nl_basics.Elem. m~10@)
                                         )
                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                          (Poly%main!nl_basics.Elem. b~4@)
                                       )))
                                      ) (Poly%main!nl_basics.Elem. m~10@)
                                  ))))
                                  (and
                                   (=>
                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                    (=>
                                     %%location_label%%7
                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_7_0~564@) (Poly%main!nl_basics.Elem.
                                       temp_7_1~619@
                                   ))))
                                   (=>
                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_7_0~564@) (Poly%main!nl_basics.Elem.
                                      temp_7_1~619@
                                    ))
                                    (=>
                                     (= temp_8_0~666@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                         (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                           (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. m~10@)
                                        )))
                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                         (Poly%main!nl_basics.Elem. b~4@)
                                     ))))
                                     (=>
                                      (= temp_8_1~716@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                          (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                            (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. d~8@)
                                              (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                  (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                    (Poly%main!nl_basics.Elem. c~6@)
                                                   )
                                                  ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. a~2@)
                                                    (Poly%main!nl_basics.Elem. c~6@)
                                                 )))
                                                ) (Poly%main!nl_basics.Elem. m~10@)
                                             )))
                                            ) (Poly%main!nl_basics.Elem. m~10@)
                                         )))
                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                          (Poly%main!nl_basics.Elem. b~4@)
                                      ))))
                                      (and
                                       (=>
                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                        (=>
                                         %%location_label%%8
                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_8_0~666@) (Poly%main!nl_basics.Elem.
                                           temp_8_1~716@
                                       ))))
                                       (=>
                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_8_0~666@) (Poly%main!nl_basics.Elem.
                                          temp_8_1~716@
                                        ))
                                        (=>
                                         (= temp_9_0~758@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                             (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. a~2@)
                                            )
                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                             (Poly%main!nl_basics.Elem. c~6@)
                                         ))))
                                         (=>
                                          (= temp_9_1~778@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                              (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. d~8@)
                                             )
                                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                              (Poly%main!nl_basics.Elem. c~6@)
                                          ))))
                                          (and
                                           (=>
                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                            (=>
                                             %%location_label%%9
                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_9_0~758@) (Poly%main!nl_basics.Elem.
                                               temp_9_1~778@
                                           ))))
                                           (=>
                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_9_0~758@) (Poly%main!nl_basics.Elem.
                                              temp_9_1~778@
                                            ))
                                            (=>
                                             (= temp_10_0~820@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                 (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. b~4@)
                                                )
                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                 (Poly%main!nl_basics.Elem. c~6@)
                                             ))))
                                             (=>
                                              (= temp_10_1~840@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                  (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. b~4@)
                                                 )
                                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                  (Poly%main!nl_basics.Elem. c~6@)
                                              ))))
                                              (and
                                               (=>
                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                (=>
                                                 %%location_label%%10
                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_10_0~820@) (Poly%main!nl_basics.Elem.
                                                   temp_10_1~840@
                                               ))))
                                               (=>
                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_10_0~820@) (Poly%main!nl_basics.Elem.
                                                  temp_10_1~840@
                                                ))
                                                (=>
                                                 (= temp_11_0~892@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                     (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                       (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. b~4@)
                                                         (Poly%main!nl_basics.Elem. m~10@)
                                                      )))
                                                     ) (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. b~4@)
                                                       (Poly%main!nl_basics.Elem. a~2@)
                                                    )))
                                                   ) (Poly%main!nl_basics.Elem. m~10@)
                                                 ))
                                                 (=>
                                                  (= temp_11_1~952@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                      (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                        (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                            (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                              (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                  (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                    (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. m~10@)
                                                                 )))
                                                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                  (Poly%main!nl_basics.Elem. c~6@)
                                                               )))
                                                              ) (Poly%main!nl_basics.Elem. m~10@)
                                                           )))
                                                          ) (Poly%main!nl_basics.Elem. m~10@)
                                                       )))
                                                      ) (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. b~4@)
                                                        (Poly%main!nl_basics.Elem. a~2@)
                                                     )))
                                                    ) (Poly%main!nl_basics.Elem. m~10@)
                                                  ))
                                                  (and
                                                   (=>
                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                    (=>
                                                     %%location_label%%11
                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_11_0~892@) (Poly%main!nl_basics.Elem.
                                                       temp_11_1~952@
                                                   ))))
                                                   (=>
                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_11_0~892@) (Poly%main!nl_basics.Elem.
                                                      temp_11_1~952@
                                                    ))
                                                    (=>
                                                     (= temp_12_0~994@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                         (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. b~4@)
                                                        )
                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                         (Poly%main!nl_basics.Elem. a~2@)
                                                     ))))
                                                     (=>
                                                      (= temp_12_1~1014@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                          (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. b~4@)
                                                         )
                                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                          (Poly%main!nl_basics.Elem. d~8@)
                                                      ))))
                                                      (and
                                                       (=>
                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                        (=>
                                                         %%location_label%%12
                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_12_0~994@) (Poly%main!nl_basics.Elem.
                                                           temp_12_1~1014@
                                                       ))))
                                                       (=>
                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_12_0~994@) (Poly%main!nl_basics.Elem.
                                                          temp_12_1~1014@
                                                        ))
                                                        (=>
                                                         (= temp_13_0~1056@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                             (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. d~8@)
                                                            )
                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                             (Poly%main!nl_basics.Elem. a~2@)
                                                         ))))
                                                         (=>
                                                          (= temp_13_1~1076@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                              (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                (Poly%main!nl_basics.Elem. d~8@)
                                                               )
                                                              ) (Poly%main!nl_basics.Elem. d~8@)
                                                             )
                                                            ) (Poly%main!nl_basics.Elem. a~2@)
                                                          ))
                                                          (and
                                                           (=>
                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                            (=>
                                                             %%location_label%%13
                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_13_0~1056@) (Poly%main!nl_basics.Elem.
                                                               temp_13_1~1076@
                                                           ))))
                                                           (=>
                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_13_0~1056@) (Poly%main!nl_basics.Elem.
                                                              temp_13_1~1076@
                                                            ))
                                                            (=>
                                                             (= temp_14_0~1123@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                 (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                   (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. m~10@)
                                                                )))
                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                 (Poly%main!nl_basics.Elem. b~4@)
                                                             ))))
                                                             (=>
                                                              (= temp_14_1~1148@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                  (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. b~4@)
                                                                 )
                                                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                  (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                    (Poly%main!nl_basics.Elem. m~10@)
                                                              ))))))
                                                              (and
                                                               (=>
                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                (=>
                                                                 %%location_label%%14
                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_14_0~1123@) (Poly%main!nl_basics.Elem.
                                                                   temp_14_1~1148@
                                                               ))))
                                                               (=>
                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_14_0~1123@) (Poly%main!nl_basics.Elem.
                                                                  temp_14_1~1148@
                                                                ))
                                                                (=>
                                                                 (= temp_15_0~1197@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                     (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. c~6@)
                                                                    )
                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.as_elem.?
                                                                       (I 85)
                                                                      )
                                                                     ) (Poly%main!nl_basics.Elem. d~8@)
                                                                 ))))
                                                                 (=>
                                                                  (= temp_15_1~1224@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                      (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. a~2@)
                                                                     )
                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.as_elem.?
                                                                        (I 85)
                                                                       )
                                                                      ) (Poly%main!nl_basics.Elem. d~8@)
                                                                  ))))
                                                                  (and
                                                                   (=>
                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                    (=>
                                                                     %%location_label%%15
                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_15_0~1197@) (Poly%main!nl_basics.Elem.
                                                                       temp_15_1~1224@
                                                                   ))))
                                                                   (=>
                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_15_0~1197@) (Poly%main!nl_basics.Elem.
                                                                      temp_15_1~1224@
                                                                    ))
                                                                    (=>
                                                                     (= temp_16_0~1271@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                         (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. a~2@)
                                                                        )
                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                         (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                           (Poly%main!nl_basics.Elem. m~10@)
                                                                     ))))))
                                                                     (=>
                                                                      (= temp_16_1~1296@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                          (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                            (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. m~10@)
                                                                         )))
                                                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                          (Poly%main!nl_basics.Elem. a~2@)
                                                                      ))))
                                                                      (and
                                                                       (=>
                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                        (=>
                                                                         %%location_label%%16
                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_16_0~1271@) (Poly%main!nl_basics.Elem.
                                                                           temp_16_1~1296@
                                                                       ))))
                                                                       (=>
                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_16_0~1271@) (Poly%main!nl_basics.Elem.
                                                                          temp_16_1~1296@
                                                                        ))
                                                                        (=>
                                                                         (= temp_17_0~1343@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                             (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                               (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. m~10@)
                                                                            )))
                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                             (Poly%main!nl_basics.Elem. b~4@)
                                                                         ))))
                                                                         (=>
                                                                          (= temp_17_1~1393@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                              (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                  (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                      (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                        (Poly%main!nl_basics.Elem. d~8@)
                                                                                       )
                                                                                      ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                        (Poly%main!nl_basics.Elem. a~2@)
                                                                                     )))
                                                                                    ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                 )))
                                                                                ) (Poly%main!nl_basics.Elem. m~10@)
                                                                             )))
                                                                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                              (Poly%main!nl_basics.Elem. b~4@)
                                                                          ))))
                                                                          (and
                                                                           (=>
                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                            (=>
                                                                             %%location_label%%17
                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_17_0~1343@) (Poly%main!nl_basics.Elem.
                                                                               temp_17_1~1393@
                                                                           ))))
                                                                           (=>
                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_17_0~1343@) (Poly%main!nl_basics.Elem.
                                                                              temp_17_1~1393@
                                                                            ))
                                                                            (=>
                                                                             (= temp_18_0~1440@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                 (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                   (Poly%main!nl_basics.Elem. m~10@)
                                                                                  )
                                                                                 ) (Poly%main!nl_basics.Elem. d~8@)
                                                                                )
                                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                 (Poly%main!nl_basics.Elem. a~2@)
                                                                             ))))
                                                                             (=>
                                                                              (= temp_18_1~1495@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                  (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                                      (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                        (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                            (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                              (Poly%main!nl_basics.Elem. b~4@)
                                                                                             )
                                                                                            ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                           )
                                                                                          ) (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                            (Poly%main!nl_basics.Elem. d~8@)
                                                                                         )))
                                                                                        ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                     )))
                                                                                    ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                   )
                                                                                  ) (Poly%main!nl_basics.Elem. d~8@)
                                                                                 )
                                                                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                  (Poly%main!nl_basics.Elem. a~2@)
                                                                              ))))
                                                                              (and
                                                                               (=>
                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                (=>
                                                                                 %%location_label%%18
                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_18_0~1440@) (Poly%main!nl_basics.Elem.
                                                                                   temp_18_1~1495@
                                                                               ))))
                                                                               (=>
                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_18_0~1440@) (Poly%main!nl_basics.Elem.
                                                                                  temp_18_1~1495@
                                                                                ))
                                                                                (=>
                                                                                 (= temp_19_0~1542@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                     (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                       (Poly%main!nl_basics.Elem. m~10@)
                                                                                      )
                                                                                     ) (Poly%main!nl_basics.Elem. d~8@)
                                                                                    )
                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                     (Poly%main!nl_basics.Elem. b~4@)
                                                                                 ))))
                                                                                 (=>
                                                                                  (= temp_19_1~1567@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                      (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                        (Poly%main!nl_basics.Elem. m~10@)
                                                                                       )
                                                                                      ) (Poly%main!nl_basics.Elem. d~8@)
                                                                                     )
                                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                      (Poly%main!nl_basics.Elem. c~6@)
                                                                                  ))))
                                                                                  (and
                                                                                   (=>
                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                    (=>
                                                                                     %%location_label%%19
                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_19_0~1542@) (Poly%main!nl_basics.Elem.
                                                                                       temp_19_1~1567@
                                                                                   ))))
                                                                                   (=>
                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_19_0~1542@) (Poly%main!nl_basics.Elem.
                                                                                      temp_19_1~1567@
                                                                                    ))
                                                                                    (=>
                                                                                     (= temp_20_0~1619@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                         (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                           (Poly%main!nl_basics.Elem. b~4@)
                                                                                          )
                                                                                         ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                        )
                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                           (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                          )
                                                                                         ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                     ))))
                                                                                     (=>
                                                                                      (= temp_20_1~1649@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                          (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                            (Poly%main!nl_basics.Elem. b~4@)
                                                                                           )
                                                                                          ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                         )
                                                                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                            (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                           )
                                                                                          ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                      ))))
                                                                                      (and
                                                                                       (=>
                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                        (=>
                                                                                         %%location_label%%20
                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_20_0~1619@) (Poly%main!nl_basics.Elem.
                                                                                           temp_20_1~1649@
                                                                                       ))))
                                                                                       (=>
                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_20_0~1619@) (Poly%main!nl_basics.Elem.
                                                                                          temp_20_1~1649@
                                                                                        ))
                                                                                        (=>
                                                                                         (= temp_21_0~1691@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                             (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                            )
                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                             (Poly%main!nl_basics.Elem. d~8@)
                                                                                         ))))
                                                                                         (=>
                                                                                          (= temp_21_1~1711@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                              (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                             )
                                                                                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                              (Poly%main!nl_basics.Elem. b~4@)
                                                                                          ))))
                                                                                          (and
                                                                                           (=>
                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                            (=>
                                                                                             %%location_label%%21
                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_21_0~1691@) (Poly%main!nl_basics.Elem.
                                                                                               temp_21_1~1711@
                                                                                           ))))
                                                                                           (=>
                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_21_0~1691@) (Poly%main!nl_basics.Elem.
                                                                                              temp_21_1~1711@
                                                                                            ))
                                                                                            (=>
                                                                                             (= temp_22_0~1758@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                 (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                   (Poly%main!nl_basics.Elem. a~2@)
                                                                                                  )
                                                                                                 ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                   (Poly%main!nl_basics.Elem. a~2@)
                                                                                                )))
                                                                                               ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                             ))
                                                                                             (=>
                                                                                              (= temp_22_1~1808@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                                                  (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                      (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                        (Poly%main!nl_basics.Elem. c~6@)
                                                                                                       )
                                                                                                      ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                        (Poly%main!nl_basics.Elem. c~6@)
                                                                                                     )))
                                                                                                    ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                   )
                                                                                                  ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                      (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                     )
                                                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                      (Poly%main!nl_basics.Elem. a~2@)
                                                                                                 )))))
                                                                                                ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                              ))
                                                                                              (and
                                                                                               (=>
                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                (=>
                                                                                                 %%location_label%%22
                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_22_0~1758@) (Poly%main!nl_basics.Elem.
                                                                                                   temp_22_1~1808@
                                                                                               ))))
                                                                                               (=>
                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_22_0~1758@) (Poly%main!nl_basics.Elem.
                                                                                                  temp_22_1~1808@
                                                                                                ))
                                                                                                (=>
                                                                                                 (= temp_23_0~1850@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                     (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                    )
                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                     (Poly%main!nl_basics.Elem. a~2@)
                                                                                                 ))))
                                                                                                 (=>
                                                                                                  (= temp_23_1~1870@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                      (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                     )
                                                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                      (Poly%main!nl_basics.Elem. b~4@)
                                                                                                  ))))
                                                                                                  (and
                                                                                                   (=>
                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                    (=>
                                                                                                     %%location_label%%23
                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_23_0~1850@) (Poly%main!nl_basics.Elem.
                                                                                                       temp_23_1~1870@
                                                                                                   ))))
                                                                                                   (=>
                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_23_0~1850@) (Poly%main!nl_basics.Elem.
                                                                                                      temp_23_1~1870@
                                                                                                    ))
                                                                                                    (=>
                                                                                                     (= temp_24_0~1912@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                         (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                        )
                                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                         (Poly%main!nl_basics.Elem. b~4@)
                                                                                                     ))))
                                                                                                     (=>
                                                                                                      (= temp_24_1~1932@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem.
                                                                                                         (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem.
                                                                                                           (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem.
                                                                                                             b~4@
                                                                                                      )))))))
                                                                                                      (and
                                                                                                       (=>
                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                        (=>
                                                                                                         %%location_label%%24
                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_24_0~1912@) (Poly%main!nl_basics.Elem.
                                                                                                           temp_24_1~1932@
                                                                                                       ))))
                                                                                                       (=>
                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_24_0~1912@) (Poly%main!nl_basics.Elem.
                                                                                                          temp_24_1~1932@
                                                                                                        ))
                                                                                                        (=>
                                                                                                         (= temp_25_0~1974@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                             (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                            )
                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                             (Poly%main!nl_basics.Elem. c~6@)
                                                                                                         ))))
                                                                                                         (=>
                                                                                                          (= temp_25_1~1994@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                              (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                (Poly%main!nl_basics.Elem. d~8@)
                                                                                                               )
                                                                                                              ) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                             )
                                                                                                            ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                          ))
                                                                                                          (and
                                                                                                           (=>
                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                            (=>
                                                                                                             %%location_label%%25
                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_25_0~1974@) (Poly%main!nl_basics.Elem.
                                                                                                               temp_25_1~1994@
                                                                                                           ))))
                                                                                                           (=>
                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_25_0~1974@) (Poly%main!nl_basics.Elem.
                                                                                                              temp_25_1~1994@
                                                                                                            ))
                                                                                                            (=>
                                                                                                             (= temp_26_0~2046@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                 (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                     (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                    )
                                                                                                                   ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                  )
                                                                                                                 ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                )
                                                                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                 (Poly%main!nl_basics.Elem. c~6@)
                                                                                                             ))))
                                                                                                             (=>
                                                                                                              (= temp_26_1~2076@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                  (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                    (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                      (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                   )))
                                                                                                                  ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                 )
                                                                                                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                  (Poly%main!nl_basics.Elem. c~6@)
                                                                                                              ))))
                                                                                                              (and
                                                                                                               (=>
                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                (=>
                                                                                                                 %%location_label%%26
                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_26_0~2046@) (Poly%main!nl_basics.Elem.
                                                                                                                   temp_26_1~2076@
                                                                                                               ))))
                                                                                                               (=>
                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_26_0~2046@) (Poly%main!nl_basics.Elem.
                                                                                                                  temp_26_1~2076@
                                                                                                                ))
                                                                                                                (=>
                                                                                                                 (= temp_27_0~2123@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                     (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                       (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                      )
                                                                                                                     ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                    )
                                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                     (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                 ))))
                                                                                                                 (=>
                                                                                                                  (= temp_27_1~2148@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                      (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                     )
                                                                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                        (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                       )
                                                                                                                      ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                  ))))
                                                                                                                  (and
                                                                                                                   (=>
                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                    (=>
                                                                                                                     %%location_label%%27
                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_27_0~2123@) (Poly%main!nl_basics.Elem.
                                                                                                                       temp_27_1~2148@
                                                                                                                   ))))
                                                                                                                   (=>
                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_27_0~2123@) (Poly%main!nl_basics.Elem.
                                                                                                                      temp_27_1~2148@
                                                                                                                    ))
                                                                                                                    (=>
                                                                                                                     (= temp_28_0~2200@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                         (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                           (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                          )
                                                                                                                         ) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                        )
                                                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                         (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                           (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                     ))))))
                                                                                                                     (=>
                                                                                                                      (= temp_28_1~2230@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                          (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                            (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                           )
                                                                                                                          ) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                         )
                                                                                                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                            (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                           )
                                                                                                                          ) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                      ))))
                                                                                                                      (and
                                                                                                                       (=>
                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                        (=>
                                                                                                                         %%location_label%%28
                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_28_0~2200@) (Poly%main!nl_basics.Elem.
                                                                                                                           temp_28_1~2230@
                                                                                                                       ))))
                                                                                                                       (=>
                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_28_0~2200@) (Poly%main!nl_basics.Elem.
                                                                                                                          temp_28_1~2230@
                                                                                                                        ))
                                                                                                                        (=>
                                                                                                                         (= temp_29_0~2277@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                             (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                            )
                                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                             (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                               (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                         ))))))
                                                                                                                         (=>
                                                                                                                          (= temp_29_1~2302@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                              (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                             )
                                                                                                                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                              (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                          ))))))
                                                                                                                          (and
                                                                                                                           (=>
                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                            (=>
                                                                                                                             %%location_label%%29
                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_29_0~2277@) (Poly%main!nl_basics.Elem.
                                                                                                                               temp_29_1~2302@
                                                                                                                           ))))
                                                                                                                           (=>
                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_29_0~2277@) (Poly%main!nl_basics.Elem.
                                                                                                                              temp_29_1~2302@
                                                                                                                            ))
                                                                                                                            (=>
                                                                                                                             (= temp_30_0~2344@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                 (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                )
                                                                                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                 (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                             ))))
                                                                                                                             (=>
                                                                                                                              (= temp_30_1~2364@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                  (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                 )
                                                                                                                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                  (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                              ))))
                                                                                                                              (and
                                                                                                                               (=>
                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                (=>
                                                                                                                                 %%location_label%%30
                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_30_0~2344@) (Poly%main!nl_basics.Elem.
                                                                                                                                   temp_30_1~2364@
                                                                                                                               ))))
                                                                                                                               (=>
                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_30_0~2344@) (Poly%main!nl_basics.Elem.
                                                                                                                                  temp_30_1~2364@
                                                                                                                                ))
                                                                                                                                (=>
                                                                                                                                 (= temp_31_0~2411@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                                     (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                       (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                    )))
                                                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                     (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                 ))))
                                                                                                                                 (=>
                                                                                                                                  (= temp_31_1~2436@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                                      (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                        (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                     )))
                                                                                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                      (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                  ))))
                                                                                                                                  (and
                                                                                                                                   (=>
                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                    (=>
                                                                                                                                     %%location_label%%31
                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_31_0~2411@) (Poly%main!nl_basics.Elem.
                                                                                                                                       temp_31_1~2436@
                                                                                                                                   ))))
                                                                                                                                   (=>
                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_31_0~2411@) (Poly%main!nl_basics.Elem.
                                                                                                                                      temp_31_1~2436@
                                                                                                                                    ))
                                                                                                                                    (=>
                                                                                                                                     (= temp_32_0~2478@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                                                                                         (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                        )
                                                                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                         (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                     ))))
                                                                                                                                     (=>
                                                                                                                                      (= temp_32_1~2498@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                          (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                            (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                           )
                                                                                                                                          ) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                         )
                                                                                                                                        ) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                      ))
                                                                                                                                      (and
                                                                                                                                       (=>
                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                        (=>
                                                                                                                                         %%location_label%%32
                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_32_0~2478@) (Poly%main!nl_basics.Elem.
                                                                                                                                           temp_32_1~2498@
                                                                                                                                       ))))
                                                                                                                                       (=>
                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_32_0~2478@) (Poly%main!nl_basics.Elem.
                                                                                                                                          temp_32_1~2498@
                                                                                                                                        ))
                                                                                                                                        (=>
                                                                                                                                         (= temp_33_0~2540@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                                             (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                            )
                                                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                             (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                         ))))
                                                                                                                                         (=>
                                                                                                                                          (= temp_33_1~2570@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                              (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                             )))
                                                                                                                                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                              (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                          ))))))
                                                                                                                                          (and
                                                                                                                                           (=>
                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                            (=>
                                                                                                                                             %%location_label%%33
                                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_33_0~2540@) (Poly%main!nl_basics.Elem.
                                                                                                                                               temp_33_1~2570@
                                                                                                                                           ))))
                                                                                                                                           (=>
                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_33_0~2540@) (Poly%main!nl_basics.Elem.
                                                                                                                                              temp_33_1~2570@
                                                                                                                                            ))
                                                                                                                                            (=>
                                                                                                                                             (= temp_34_0~2612@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                                                                                                 (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                )
                                                                                                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                 (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                             ))))
                                                                                                                                             (=>
                                                                                                                                              (= temp_34_1~2642@ (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                  (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                    (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                 )))
                                                                                                                                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                  (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                    (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                              ))))))
                                                                                                                                              (and
                                                                                                                                               (=>
                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                (=>
                                                                                                                                                 %%location_label%%34
                                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_34_0~2612@) (Poly%main!nl_basics.Elem.
                                                                                                                                                   temp_34_1~2642@
                                                                                                                                               ))))
                                                                                                                                               (=>
                                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_34_0~2612@) (Poly%main!nl_basics.Elem.
                                                                                                                                                  temp_34_1~2642@
                                                                                                                                                ))
                                                                                                                                                (=>
                                                                                                                                                 (= temp_35_0~2689@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                     (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                       (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                      )
                                                                                                                                                     ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                       (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                    )))
                                                                                                                                                   ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                 ))
                                                                                                                                                 (=>
                                                                                                                                                  (= temp_35_1~2714@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                      (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                        (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                          (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                     )))))
                                                                                                                                                    ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                  ))
                                                                                                                                                  (and
                                                                                                                                                   (=>
                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                    (=>
                                                                                                                                                     %%location_label%%35
                                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_35_0~2689@) (Poly%main!nl_basics.Elem.
                                                                                                                                                       temp_35_1~2714@
                                                                                                                                                   ))))
                                                                                                                                                   (=>
                                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_35_0~2689@) (Poly%main!nl_basics.Elem.
                                                                                                                                                      temp_35_1~2714@
                                                                                                                                                    ))
                                                                                                                                                    (=>
                                                                                                                                                     (= temp_36_0~2751@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem.
                                                                                                                                                        (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem.
                                                                                                                                                          b~4@
                                                                                                                                                     )))))
                                                                                                                                                     (=>
                                                                                                                                                      (= temp_36_1~2766@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem.
                                                                                                                                                         (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem.
                                                                                                                                                           a~2@
                                                                                                                                                      )))))
                                                                                                                                                      (and
                                                                                                                                                       (=>
                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                        (=>
                                                                                                                                                         %%location_label%%36
                                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_36_0~2751@) (Poly%main!nl_basics.Elem.
                                                                                                                                                           temp_36_1~2766@
                                                                                                                                                       ))))
                                                                                                                                                       (=>
                                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_36_0~2751@) (Poly%main!nl_basics.Elem.
                                                                                                                                                          temp_36_1~2766@
                                                                                                                                                        ))
                                                                                                                                                        (=>
                                                                                                                                                         (= temp_37_0~2808@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                             (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                            )
                                                                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                             (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                         ))))
                                                                                                                                                         (=>
                                                                                                                                                          (= temp_37_1~2828@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                              (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                             )
                                                                                                                                                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                              (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                          ))))
                                                                                                                                                          (and
                                                                                                                                                           (=>
                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                            (=>
                                                                                                                                                             %%location_label%%37
                                                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_37_0~2808@) (Poly%main!nl_basics.Elem.
                                                                                                                                                               temp_37_1~2828@
                                                                                                                                                           ))))
                                                                                                                                                           (=>
                                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_37_0~2808@) (Poly%main!nl_basics.Elem.
                                                                                                                                                              temp_37_1~2828@
                                                                                                                                                            ))
                                                                                                                                                            (=>
                                                                                                                                                             (= temp_38_0~2875@ (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                 (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                )
                                                                                                                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                   (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                  )
                                                                                                                                                                 ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                             ))))
                                                                                                                                                             (=>
                                                                                                                                                              (= temp_38_1~2900@ (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
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
                                                                                                                                                                 %%location_label%%38
                                                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_38_0~2875@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                   temp_38_1~2900@
                                                                                                                                                               ))))
                                                                                                                                                               (=>
                                                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_38_0~2875@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                  temp_38_1~2900@
                                                                                                                                                                ))
                                                                                                                                                                (=>
                                                                                                                                                                 (= temp_39_0~2952@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                     (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                         (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                        )
                                                                                                                                                                       ) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                      )
                                                                                                                                                                     ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                    )
                                                                                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                     (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                 ))))
                                                                                                                                                                 (=>
                                                                                                                                                                  (= temp_39_1~2982@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                      (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                                                                          (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                            (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                           )
                                                                                                                                                                          ) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                         )
                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                       )
                                                                                                                                                                      ) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                     )
                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                  ))
                                                                                                                                                                  (and
                                                                                                                                                                   (=>
                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                    (=>
                                                                                                                                                                     %%location_label%%39
                                                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_39_0~2952@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                       temp_39_1~2982@
                                                                                                                                                                   ))))
                                                                                                                                                                   (=>
                                                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_39_0~2952@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                      temp_39_1~2982@
                                                                                                                                                                    ))
                                                                                                                                                                    (=>
                                                                                                                                                                     (= temp_40_0~3024@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                         (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                        )
                                                                                                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                         (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                     ))))
                                                                                                                                                                     (=>
                                                                                                                                                                      (= temp_40_1~3044@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                         (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                           (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                             b~4@
                                                                                                                                                                      )))))))
                                                                                                                                                                      (and
                                                                                                                                                                       (=>
                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                        (=>
                                                                                                                                                                         %%location_label%%40
                                                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_40_0~3024@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                           temp_40_1~3044@
                                                                                                                                                                       ))))
                                                                                                                                                                       (=>
                                                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_40_0~3024@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                          temp_40_1~3044@
                                                                                                                                                                        ))
                                                                                                                                                                        (=>
                                                                                                                                                                         (= temp_41_0~3096@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                             (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                            )
                                                                                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                                                                               (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                 (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                )
                                                                                                                                                                               ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                              )
                                                                                                                                                                             ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                         ))))
                                                                                                                                                                         (=>
                                                                                                                                                                          (= temp_41_1~3121@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                              (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                             )
                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                                                                                (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                               )
                                                                                                                                                                              ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                          ))))
                                                                                                                                                                          (and
                                                                                                                                                                           (=>
                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                            (=>
                                                                                                                                                                             %%location_label%%41
                                                                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_41_0~3096@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                               temp_41_1~3121@
                                                                                                                                                                           ))))
                                                                                                                                                                           (=>
                                                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_41_0~3096@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                              temp_41_1~3121@
                                                                                                                                                                            ))
                                                                                                                                                                            (=>
                                                                                                                                                                             (= temp_42_0~3178@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                 (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                   (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                  )
                                                                                                                                                                                 ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                     (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                       (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                    )))
                                                                                                                                                                                   ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                )))
                                                                                                                                                                               ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                             ))
                                                                                                                                                                             (=>
                                                                                                                                                                              (= temp_42_1~3213@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                  (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                      (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                        (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                     )))
                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                      (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                   )))
                                                                                                                                                                                  ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                 )
                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                              ))
                                                                                                                                                                              (and
                                                                                                                                                                               (=>
                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                (=>
                                                                                                                                                                                 %%location_label%%42
                                                                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_42_0~3178@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                   temp_42_1~3213@
                                                                                                                                                                               ))))
                                                                                                                                                                               (=>
                                                                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_42_0~3178@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                  temp_42_1~3213@
                                                                                                                                                                                ))
                                                                                                                                                                                (=>
                                                                                                                                                                                 (= temp_43_0~3272@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                     (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                       (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                      )
                                                                                                                                                                                     ) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                    )
                                                                                                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                     (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.as_elem.?
                                                                                                                                                                                         (I 13)
                                                                                                                                                                                        )
                                                                                                                                                                                       ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                 ))))))
                                                                                                                                                                                 (=>
                                                                                                                                                                                  (= temp_43_1~3309@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                      (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                        (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                       )
                                                                                                                                                                                      ) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                     )
                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                        (Poly%main!nl_basics.Elem. (main!nl_basics.as_elem.? (I 13))) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                         m~10@
                                                                                                                                                                                       ))
                                                                                                                                                                                      ) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                  ))))
                                                                                                                                                                                  (and
                                                                                                                                                                                   (=>
                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                    (=>
                                                                                                                                                                                     %%location_label%%43
                                                                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_43_0~3272@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                       temp_43_1~3309@
                                                                                                                                                                                   ))))
                                                                                                                                                                                   (=>
                                                                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_43_0~3272@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                      temp_43_1~3309@
                                                                                                                                                                                    ))
                                                                                                                                                                                    (=>
                                                                                                                                                                                     (= temp_44_0~3351@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                         (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                        )
                                                                                                                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                         (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                     ))))
                                                                                                                                                                                     (=>
                                                                                                                                                                                      (= temp_44_1~3371@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                          (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                            (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                           )
                                                                                                                                                                                          ) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                         )
                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                      ))
                                                                                                                                                                                      (and
                                                                                                                                                                                       (=>
                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                        (=>
                                                                                                                                                                                         %%location_label%%44
                                                                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_44_0~3351@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                           temp_44_1~3371@
                                                                                                                                                                                       ))))
                                                                                                                                                                                       (=>
                                                                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_44_0~3351@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                          temp_44_1~3371@
                                                                                                                                                                                        ))
                                                                                                                                                                                        (=>
                                                                                                                                                                                         (= temp_45_0~3418@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                             (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                               (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                              )
                                                                                                                                                                                             ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                            )
                                                                                                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                             (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                         ))))
                                                                                                                                                                                         (=>
                                                                                                                                                                                          (= temp_45_1~3443@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                              (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                 )
                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                               )
                                                                                                                                                                                              ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                             )
                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                          ))
                                                                                                                                                                                          (and
                                                                                                                                                                                           (=>
                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                            (=>
                                                                                                                                                                                             %%location_label%%45
                                                                                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_45_0~3418@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                               temp_45_1~3443@
                                                                                                                                                                                           ))))
                                                                                                                                                                                           (=>
                                                                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_45_0~3418@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                              temp_45_1~3443@
                                                                                                                                                                                            ))
                                                                                                                                                                                            (=>
                                                                                                                                                                                             (= temp_46_0~3485@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                )
                                                                                                                                                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                             ))))
                                                                                                                                                                                             (=>
                                                                                                                                                                                              (= temp_46_1~3505@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                 )
                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                              ))))
                                                                                                                                                                                              (and
                                                                                                                                                                                               (=>
                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                (=>
                                                                                                                                                                                                 %%location_label%%46
                                                                                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_46_0~3485@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                   temp_46_1~3505@
                                                                                                                                                                                               ))))
                                                                                                                                                                                               (=>
                                                                                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_46_0~3485@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                  temp_46_1~3505@
                                                                                                                                                                                                ))
                                                                                                                                                                                                (=>
                                                                                                                                                                                                 (= temp_47_0~3552@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                    )
                                                                                                                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                       (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                      )
                                                                                                                                                                                                     ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                 ))))
                                                                                                                                                                                                 (=>
                                                                                                                                                                                                  (= temp_47_1~3607@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                     )
                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                        (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                 )
                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                               )
                                                                                                                                                                                                              ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                             )))
                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                         )))
                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                       )
                                                                                                                                                                                                      ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                  ))))
                                                                                                                                                                                                  (and
                                                                                                                                                                                                   (=>
                                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                    (=>
                                                                                                                                                                                                     %%location_label%%47
                                                                                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_47_0~3552@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                       temp_47_1~3607@
                                                                                                                                                                                                   ))))
                                                                                                                                                                                                   (=>
                                                                                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_47_0~3552@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                      temp_47_1~3607@
                                                                                                                                                                                                    ))
                                                                                                                                                                                                    (=>
                                                                                                                                                                                                     (= temp_48_0~3649@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                        )
                                                                                                                                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                     ))))
                                                                                                                                                                                                     (=>
                                                                                                                                                                                                      (= temp_48_1~3669@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                         (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                           (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                             b~4@
                                                                                                                                                                                                      )))))))
                                                                                                                                                                                                      (and
                                                                                                                                                                                                       (=>
                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                        (=>
                                                                                                                                                                                                         %%location_label%%48
                                                                                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_48_0~3649@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                           temp_48_1~3669@
                                                                                                                                                                                                       ))))
                                                                                                                                                                                                       (=>
                                                                                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_48_0~3649@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                          temp_48_1~3669@
                                                                                                                                                                                                        ))
                                                                                                                                                                                                        (=>
                                                                                                                                                                                                         (= temp_49_0~3711@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                            )
                                                                                                                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                         ))))
                                                                                                                                                                                                         (=>
                                                                                                                                                                                                          (= temp_49_1~3731@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                               )
                                                                                                                                                                                                              ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                             )
                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                          ))
                                                                                                                                                                                                          (and
                                                                                                                                                                                                           (=>
                                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                            (=>
                                                                                                                                                                                                             %%location_label%%49
                                                                                                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_49_0~3711@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                               temp_49_1~3731@
                                                                                                                                                                                                           ))))
                                                                                                                                                                                                           (=>
                                                                                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_49_0~3711@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                              temp_49_1~3731@
                                                                                                                                                                                                            ))
                                                                                                                                                                                                            (=>
                                                                                                                                                                                                             (= temp_50_0~3778@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                )
                                                                                                                                                                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                   (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                  )
                                                                                                                                                                                                                 ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                             ))))
                                                                                                                                                                                                             (=>
                                                                                                                                                                                                              (= temp_50_1~3803@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                 )
                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                    (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                   )
                                                                                                                                                                                                                  ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                              ))))
                                                                                                                                                                                                              (and
                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                 %%location_label%%50
                                                                                                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_50_0~3778@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                   temp_50_1~3803@
                                                                                                                                                                                                               ))))
                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_50_0~3778@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                  temp_50_1~3803@
                                                                                                                                                                                                                ))
                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                 (= temp_51_0~3845@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                    )
                                                                                                                                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                 ))))
                                                                                                                                                                                                                 (=>
                                                                                                                                                                                                                  (= temp_51_1~3875@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                        (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                     )))
                                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                        (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                  ))))))
                                                                                                                                                                                                                  (and
                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                     %%location_label%%51
                                                                                                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_51_0~3845@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                       temp_51_1~3875@
                                                                                                                                                                                                                   ))))
                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_51_0~3845@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                      temp_51_1~3875@
                                                                                                                                                                                                                    ))
                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                     (= temp_52_0~3917@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                        )
                                                                                                                                                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                     ))))
                                                                                                                                                                                                                     (=>
                                                                                                                                                                                                                      (= temp_52_1~3937@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                            (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                           )
                                                                                                                                                                                                                          ) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                         )
                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                      ))
                                                                                                                                                                                                                      (and
                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                         %%location_label%%52
                                                                                                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_52_0~3917@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                           temp_52_1~3937@
                                                                                                                                                                                                                       ))))
                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_52_0~3917@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                          temp_52_1~3937@
                                                                                                                                                                                                                        ))
                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                         (= temp_53_0~3984@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                               (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                              )
                                                                                                                                                                                                                             ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                            )
                                                                                                                                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                         ))))
                                                                                                                                                                                                                         (=>
                                                                                                                                                                                                                          (= temp_53_1~4019@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                 )
                                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                               )))
                                                                                                                                                                                                                              ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                             )
                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                          ))))
                                                                                                                                                                                                                          (and
                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                             %%location_label%%53
                                                                                                                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_53_0~3984@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                               temp_53_1~4019@
                                                                                                                                                                                                                           ))))
                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_53_0~3984@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                              temp_53_1~4019@
                                                                                                                                                                                                                            ))
                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                             (= temp_54_0~4061@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                )
                                                                                                                                                                                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                             ))))
                                                                                                                                                                                                                             (=>
                                                                                                                                                                                                                              (= temp_54_1~4081@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                 )
                                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                              ))))
                                                                                                                                                                                                                              (and
                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                 %%location_label%%54
                                                                                                                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_54_0~4061@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                   temp_54_1~4081@
                                                                                                                                                                                                                               ))))
                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_54_0~4061@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                  temp_54_1~4081@
                                                                                                                                                                                                                                ))
                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                 (= temp_55_0~4118@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                   ) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                 ))
                                                                                                                                                                                                                                 (=>
                                                                                                                                                                                                                                  (= temp_55_1~4133@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                     (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                       c~6@
                                                                                                                                                                                                                                  )))))
                                                                                                                                                                                                                                  (and
                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                     %%location_label%%55
                                                                                                                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_55_0~4118@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                       temp_55_1~4133@
                                                                                                                                                                                                                                   ))))
                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_55_0~4118@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                      temp_55_1~4133@
                                                                                                                                                                                                                                    ))
                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                     (= temp_56_0~4175@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                     ))))
                                                                                                                                                                                                                                     (=>
                                                                                                                                                                                                                                      (= temp_56_1~4195@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                            (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                           )
                                                                                                                                                                                                                                          ) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                         )
                                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                      ))
                                                                                                                                                                                                                                      (and
                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                         %%location_label%%56
                                                                                                                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_56_0~4175@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                           temp_56_1~4195@
                                                                                                                                                                                                                                       ))))
                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_56_0~4175@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                          temp_56_1~4195@
                                                                                                                                                                                                                                        ))
                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                         (= temp_57_0~4237@ (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                         ))))
                                                                                                                                                                                                                                         (=>
                                                                                                                                                                                                                                          (= temp_57_1~4257@ (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                             )
                                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                          ))))
                                                                                                                                                                                                                                          (and
                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                             %%location_label%%57
                                                                                                                                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_57_0~4237@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                               temp_57_1~4257@
                                                                                                                                                                                                                                           ))))
                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_57_0~4237@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                              temp_57_1~4257@
                                                                                                                                                                                                                                            ))
                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                             (= temp_58_0~4304@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                   (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                 ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                             ))))
                                                                                                                                                                                                                                             (=>
                                                                                                                                                                                                                                              (= temp_58_1~4329@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                    (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                   )
                                                                                                                                                                                                                                                  ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                 )
                                                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                              ))))
                                                                                                                                                                                                                                              (and
                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                 %%location_label%%58
                                                                                                                                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_58_0~4304@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                   temp_58_1~4329@
                                                                                                                                                                                                                                               ))))
                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_58_0~4304@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                  temp_58_1~4329@
                                                                                                                                                                                                                                                ))
                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                 (= temp_59_0~4371@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                 ))))
                                                                                                                                                                                                                                                 (=>
                                                                                                                                                                                                                                                  (= temp_59_1~4391@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                     )
                                                                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                  ))))
                                                                                                                                                                                                                                                  (and
                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                     %%location_label%%59
                                                                                                                                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_59_0~4371@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                       temp_59_1~4391@
                                                                                                                                                                                                                                                   ))))
                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_59_0~4371@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                      temp_59_1~4391@
                                                                                                                                                                                                                                                    ))
                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                     (= temp_60_0~4433@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                     ))))
                                                                                                                                                                                                                                                     (=>
                                                                                                                                                                                                                                                      (= temp_60_1~4453@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                         )
                                                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                      ))))
                                                                                                                                                                                                                                                      (and
                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                         %%location_label%%60
                                                                                                                                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_60_0~4433@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                           temp_60_1~4453@
                                                                                                                                                                                                                                                       ))))
                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_60_0~4433@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                          temp_60_1~4453@
                                                                                                                                                                                                                                                        ))
                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                         (= temp_61_0~4500@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                               (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                             ) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                         ))))
                                                                                                                                                                                                                                                         (=>
                                                                                                                                                                                                                                                          (= temp_61_1~4562@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                             )
                                                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.as_elem.?
                                                                                                                                                                                                                                                                          (I 48)
                                                                                                                                                                                                                                                                         )
                                                                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                       )))
                                                                                                                                                                                                                                                                      ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                        (Poly%main!nl_basics.Elem. d~8@)
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
                                                                                                                                                                                                                                                             %%location_label%%61
                                                                                                                                                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_61_0~4500@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                               temp_61_1~4562@
                                                                                                                                                                                                                                                           ))))
                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_61_0~4500@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                              temp_61_1~4562@
                                                                                                                                                                                                                                                            ))
                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                             (= temp_62_0~4604@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                             ))))
                                                                                                                                                                                                                                                             (=>
                                                                                                                                                                                                                                                              (= temp_62_1~4624@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                 )
                                                                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                              ))))
                                                                                                                                                                                                                                                              (and
                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                 %%location_label%%62
                                                                                                                                                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_62_0~4604@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                   temp_62_1~4624@
                                                                                                                                                                                                                                                               ))))
                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_62_0~4604@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                  temp_62_1~4624@
                                                                                                                                                                                                                                                                ))
                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                 (= temp_63_0~4676@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                       (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                     ) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                       (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                     ) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                 ))))
                                                                                                                                                                                                                                                                 (=>
                                                                                                                                                                                                                                                                  (= temp_63_1~4706@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                         )
                                                                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                       )
                                                                                                                                                                                                                                                                      ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                        (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                     )))
                                                                                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                  ))
                                                                                                                                                                                                                                                                  (and
                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                     %%location_label%%63
                                                                                                                                                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_63_0~4676@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                       temp_63_1~4706@
                                                                                                                                                                                                                                                                   ))))
                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_63_0~4676@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                      temp_63_1~4706@
                                                                                                                                                                                                                                                                    ))
                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                     (= temp_64_0~4758@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                                                           ) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                         ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                     ))))
                                                                                                                                                                                                                                                                     (=>
                                                                                                                                                                                                                                                                      (= temp_64_1~4788@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                               )
                                                                                                                                                                                                                                                                              ) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                             )
                                                                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                           )
                                                                                                                                                                                                                                                                          ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                         )
                                                                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                      ))
                                                                                                                                                                                                                                                                      (and
                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                         %%location_label%%64
                                                                                                                                                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_64_0~4758@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                           temp_64_1~4788@
                                                                                                                                                                                                                                                                       ))))
                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_64_0~4758@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                          temp_64_1~4788@
                                                                                                                                                                                                                                                                        ))
                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                         (= temp_65_0~4837@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. (main!nl_basics.as_elem.? (I 5))) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                              d~8@
                                                                                                                                                                                                                                                                            ))
                                                                                                                                                                                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                         ))))
                                                                                                                                                                                                                                                                         (=>
                                                                                                                                                                                                                                                                          (= temp_65_1~4864@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.as_elem.?
                                                                                                                                                                                                                                                                              (I 5)
                                                                                                                                                                                                                                                                             )
                                                                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                          ))))))
                                                                                                                                                                                                                                                                          (and
                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                             %%location_label%%65
                                                                                                                                                                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_65_0~4837@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                               temp_65_1~4864@
                                                                                                                                                                                                                                                                           ))))
                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_65_0~4837@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                              temp_65_1~4864@
                                                                                                                                                                                                                                                                            ))
                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                             (= temp_66_0~4918@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.as_elem.?
                                                                                                                                                                                                                                                                                   (I 45)
                                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                                 ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                   (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                             ))))))
                                                                                                                                                                                                                                                                             (=>
                                                                                                                                                                                                                                                                              (= temp_66_1~4980@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                 )
                                                                                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.as_elem.?
                                                                                                                                                                                                                                                                                    (I 45)
                                                                                                                                                                                                                                                                                   )
                                                                                                                                                                                                                                                                                  ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                        (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                            (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                             )
                                                                                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                           )))
                                                                                                                                                                                                                                                                                          ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                         )
                                                                                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                     )))
                                                                                                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                              ))))))
                                                                                                                                                                                                                                                                              (and
                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                 %%location_label%%66
                                                                                                                                                                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_66_0~4918@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                   temp_66_1~4980@
                                                                                                                                                                                                                                                                               ))))
                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_66_0~4918@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                  temp_66_1~4980@
                                                                                                                                                                                                                                                                                ))
                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                 (= temp_67_0~5022@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                 ))))
                                                                                                                                                                                                                                                                                 (=>
                                                                                                                                                                                                                                                                                  (= temp_67_1~5042@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                     )
                                                                                                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                  ))))
                                                                                                                                                                                                                                                                                  (and
                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                     %%location_label%%67
                                                                                                                                                                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_67_0~5022@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                       temp_67_1~5042@
                                                                                                                                                                                                                                                                                   ))))
                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_67_0~5022@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                      temp_67_1~5042@
                                                                                                                                                                                                                                                                                    ))
                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                     (= temp_68_0~5084@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                     ))))
                                                                                                                                                                                                                                                                                     (=>
                                                                                                                                                                                                                                                                                      (= temp_68_1~5104@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                         )
                                                                                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                      ))))
                                                                                                                                                                                                                                                                                      (and
                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                         %%location_label%%68
                                                                                                                                                                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_68_0~5084@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                           temp_68_1~5104@
                                                                                                                                                                                                                                                                                       ))))
                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_68_0~5084@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                          temp_68_1~5104@
                                                                                                                                                                                                                                                                                        ))
                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                         (= temp_69_0~5146@ (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                         ))))
                                                                                                                                                                                                                                                                                         (=>
                                                                                                                                                                                                                                                                                          (= temp_69_1~5166@ (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                             )
                                                                                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                          ))))
                                                                                                                                                                                                                                                                                          (and
                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                             %%location_label%%69
                                                                                                                                                                                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_69_0~5146@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                               temp_69_1~5166@
                                                                                                                                                                                                                                                                                           ))))
                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_69_0~5146@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                              temp_69_1~5166@
                                                                                                                                                                                                                                                                                            ))
                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                             (= temp_70_0~5208@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                             ))))
                                                                                                                                                                                                                                                                                             (=>
                                                                                                                                                                                                                                                                                              (= temp_70_1~5228@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                 (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                   (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                     a~2@
                                                                                                                                                                                                                                                                                              )))))))
                                                                                                                                                                                                                                                                                              (and
                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                 %%location_label%%70
                                                                                                                                                                                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_70_0~5208@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                   temp_70_1~5228@
                                                                                                                                                                                                                                                                                               ))))
                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_70_0~5208@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                  temp_70_1~5228@
                                                                                                                                                                                                                                                                                                ))
                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                 (= temp_71_0~5270@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                 ))))
                                                                                                                                                                                                                                                                                                 (=>
                                                                                                                                                                                                                                                                                                  (= temp_71_1~5290@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                        (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                       )
                                                                                                                                                                                                                                                                                                      ) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                     )
                                                                                                                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                  ))
                                                                                                                                                                                                                                                                                                  (and
                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                     %%location_label%%71
                                                                                                                                                                                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_71_0~5270@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                       temp_71_1~5290@
                                                                                                                                                                                                                                                                                                   ))))
                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_71_0~5270@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                      temp_71_1~5290@
                                                                                                                                                                                                                                                                                                    ))
                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                     (= temp_72_0~5332@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                     ))))
                                                                                                                                                                                                                                                                                                     (=>
                                                                                                                                                                                                                                                                                                      (= temp_72_1~5352@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                         (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                           (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                             a~2@
                                                                                                                                                                                                                                                                                                      )))))))
                                                                                                                                                                                                                                                                                                      (and
                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                         %%location_label%%72
                                                                                                                                                                                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_72_0~5332@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                           temp_72_1~5352@
                                                                                                                                                                                                                                                                                                       ))))
                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_72_0~5332@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                          temp_72_1~5352@
                                                                                                                                                                                                                                                                                                        ))
                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                         (= temp_73_0~5399@ (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                               (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                                                                             ) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                         ))))
                                                                                                                                                                                                                                                                                                         (=>
                                                                                                                                                                                                                                                                                                          (= temp_73_1~5449@ (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                             )
                                                                                                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                        (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                       )
                                                                                                                                                                                                                                                                                                                      ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                        (Poly%main!nl_basics.Elem. a~2@)
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
                                                                                                                                                                                                                                                                                                             %%location_label%%73
                                                                                                                                                                                                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_73_0~5399@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                               temp_73_1~5449@
                                                                                                                                                                                                                                                                                                           ))))
                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_73_0~5399@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                              temp_73_1~5449@
                                                                                                                                                                                                                                                                                                            ))
                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                             (= temp_74_0~5496@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                   (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                                                                 ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                   (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                )))
                                                                                                                                                                                                                                                                                                               ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                             ))
                                                                                                                                                                                                                                                                                                             (=>
                                                                                                                                                                                                                                                                                                              (= temp_74_1~5521@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                    (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                   )
                                                                                                                                                                                                                                                                                                                  ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                    (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                 )))
                                                                                                                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                              ))
                                                                                                                                                                                                                                                                                                              (and
                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                 %%location_label%%74
                                                                                                                                                                                                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_74_0~5496@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                   temp_74_1~5521@
                                                                                                                                                                                                                                                                                                               ))))
                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_74_0~5496@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                  temp_74_1~5521@
                                                                                                                                                                                                                                                                                                                ))
                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                 (= temp_75_0~5568@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                       (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                                                                     ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                 ))))
                                                                                                                                                                                                                                                                                                                 (=>
                                                                                                                                                                                                                                                                                                                  (= temp_75_1~5623@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                         )
                                                                                                                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                            (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                                                                                                                                                                                                                                                                                (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                               )
                                                                                                                                                                                                                                                                                                                              ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                             )
                                                                                                                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                           )))
                                                                                                                                                                                                                                                                                                                          ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                       )))
                                                                                                                                                                                                                                                                                                                      ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                     )
                                                                                                                                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                  ))))
                                                                                                                                                                                                                                                                                                                  (and
                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                     %%location_label%%75
                                                                                                                                                                                                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_75_0~5568@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                       temp_75_1~5623@
                                                                                                                                                                                                                                                                                                                   ))))
                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_75_0~5568@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                      temp_75_1~5623@
                                                                                                                                                                                                                                                                                                                    ))
                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                     (= temp_76_0~5665@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                     ))))
                                                                                                                                                                                                                                                                                                                     (=>
                                                                                                                                                                                                                                                                                                                      (= temp_76_1~5685@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                         )
                                                                                                                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                      ))))
                                                                                                                                                                                                                                                                                                                      (and
                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                         %%location_label%%76
                                                                                                                                                                                                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_76_0~5665@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                           temp_76_1~5685@
                                                                                                                                                                                                                                                                                                                       ))))
                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_76_0~5665@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                          temp_76_1~5685@
                                                                                                                                                                                                                                                                                                                        ))
                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                         (= temp_77_0~5732@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                               (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                                                                                             ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                               (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                            )))
                                                                                                                                                                                                                                                                                                                           ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                         ))
                                                                                                                                                                                                                                                                                                                         (=>
                                                                                                                                                                                                                                                                                                                          (= temp_77_1~5792@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                     )
                                                                                                                                                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                   )
                                                                                                                                                                                                                                                                                                                                  ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                     )
                                                                                                                                                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                 )))
                                                                                                                                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                               )
                                                                                                                                                                                                                                                                                                                              ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                 )
                                                                                                                                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                             )))))
                                                                                                                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                          ))
                                                                                                                                                                                                                                                                                                                          (and
                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                                             %%location_label%%77
                                                                                                                                                                                                                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_77_0~5732@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                               temp_77_1~5792@
                                                                                                                                                                                                                                                                                                                           ))))
                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_77_0~5732@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                              temp_77_1~5792@
                                                                                                                                                                                                                                                                                                                            ))
                                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                                             (= temp_78_0~5834@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                                                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                             ))))
                                                                                                                                                                                                                                                                                                                             (=>
                                                                                                                                                                                                                                                                                                                              (= temp_78_1~5854@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                 )
                                                                                                                                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                              ))))
                                                                                                                                                                                                                                                                                                                              (and
                                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                                 %%location_label%%78
                                                                                                                                                                                                                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_78_0~5834@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                   temp_78_1~5854@
                                                                                                                                                                                                                                                                                                                               ))))
                                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_78_0~5834@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                  temp_78_1~5854@
                                                                                                                                                                                                                                                                                                                                ))
                                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                                 (= temp_79_0~5908@ (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                       (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                                                                                     ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. (main!nl_basics.as_elem.? (I 11)))
                                                                                                                                                                                                                                                                                                                                 ))))
                                                                                                                                                                                                                                                                                                                                 (=>
                                                                                                                                                                                                                                                                                                                                  (= temp_79_1~5940@ (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                        (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                       )
                                                                                                                                                                                                                                                                                                                                      ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                     )
                                                                                                                                                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.as_elem.?
                                                                                                                                                                                                                                                                                                                                        (I 11)
                                                                                                                                                                                                                                                                                                                                       )
                                                                                                                                                                                                                                                                                                                                      ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                  ))))
                                                                                                                                                                                                                                                                                                                                  (and
                                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                                     %%location_label%%79
                                                                                                                                                                                                                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_79_0~5908@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                       temp_79_1~5940@
                                                                                                                                                                                                                                                                                                                                   ))))
                                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_79_0~5908@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                      temp_79_1~5940@
                                                                                                                                                                                                                                                                                                                                    ))
                                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                                     (= temp_80_0~5989@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.as_elem.?
                                                                                                                                                                                                                                                                                                                                           (I 85)
                                                                                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                                                                                         ) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                     ))))
                                                                                                                                                                                                                                                                                                                                     (=>
                                                                                                                                                                                                                                                                                                                                      (= temp_80_1~6016@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                         (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                           (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.as_elem.? (I 85)))
                                                                                                                                                                                                                                                                                                                                            (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                      ))))))
                                                                                                                                                                                                                                                                                                                                      (and
                                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                                         %%location_label%%80
                                                                                                                                                                                                                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_80_0~5989@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                           temp_80_1~6016@
                                                                                                                                                                                                                                                                                                                                       ))))
                                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_80_0~5989@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                          temp_80_1~6016@
                                                                                                                                                                                                                                                                                                                                        ))
                                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                                         (= temp_81_0~6058@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                         ))))
                                                                                                                                                                                                                                                                                                                                         (=>
                                                                                                                                                                                                                                                                                                                                          (= temp_81_1~6078@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                             (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                               (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                 a~2@
                                                                                                                                                                                                                                                                                                                                          )))))))
                                                                                                                                                                                                                                                                                                                                          (and
                                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                                                             %%location_label%%81
                                                                                                                                                                                                                                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_81_0~6058@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                               temp_81_1~6078@
                                                                                                                                                                                                                                                                                                                                           ))))
                                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_81_0~6058@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                              temp_81_1~6078@
                                                                                                                                                                                                                                                                                                                                            ))
                                                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                                                             (= temp_82_0~6125@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                                                                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                   (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                                                                                                 ) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                             ))))
                                                                                                                                                                                                                                                                                                                                             (=>
                                                                                                                                                                                                                                                                                                                                              (= temp_82_1~6150@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                 )
                                                                                                                                                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                    (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                   )
                                                                                                                                                                                                                                                                                                                                                  ) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                              ))))
                                                                                                                                                                                                                                                                                                                                              (and
                                                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                                                 %%location_label%%82
                                                                                                                                                                                                                                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_82_0~6125@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                   temp_82_1~6150@
                                                                                                                                                                                                                                                                                                                                               ))))
                                                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_82_0~6125@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                  temp_82_1~6150@
                                                                                                                                                                                                                                                                                                                                                ))
                                                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                                                 (= temp_83_0~6192@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                 ))))
                                                                                                                                                                                                                                                                                                                                                 (=>
                                                                                                                                                                                                                                                                                                                                                  (= temp_83_1~6222@ (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                        (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                       )
                                                                                                                                                                                                                                                                                                                                                      ) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                     )
                                                                                                                                                                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                        (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                       )
                                                                                                                                                                                                                                                                                                                                                      ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                  ))))
                                                                                                                                                                                                                                                                                                                                                  (and
                                                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                                                     %%location_label%%83
                                                                                                                                                                                                                                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_83_0~6192@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                       temp_83_1~6222@
                                                                                                                                                                                                                                                                                                                                                   ))))
                                                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_83_0~6192@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                      temp_83_1~6222@
                                                                                                                                                                                                                                                                                                                                                    ))
                                                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                                                     (= temp_84_0~6279@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                                                                                                                                           ) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                                                                                                         ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                                                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                           (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                     ))))))
                                                                                                                                                                                                                                                                                                                                                     (=>
                                                                                                                                                                                                                                                                                                                                                      (= temp_84_1~6314@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                               )
                                                                                                                                                                                                                                                                                                                                                              ) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                             )
                                                                                                                                                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                           )
                                                                                                                                                                                                                                                                                                                                                          ) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                         )
                                                                                                                                                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                      ))))
                                                                                                                                                                                                                                                                                                                                                      (and
                                                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                                                         %%location_label%%84
                                                                                                                                                                                                                                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_84_0~6279@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                           temp_84_1~6314@
                                                                                                                                                                                                                                                                                                                                                       ))))
                                                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_84_0~6279@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                          temp_84_1~6314@
                                                                                                                                                                                                                                                                                                                                                        ))
                                                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                                                         (= temp_85_0~6356@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                                                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                         ))))
                                                                                                                                                                                                                                                                                                                                                         (=>
                                                                                                                                                                                                                                                                                                                                                          (= temp_85_1~6376@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                             )
                                                                                                                                                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                          ))))
                                                                                                                                                                                                                                                                                                                                                          (and
                                                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                                                                             %%location_label%%85
                                                                                                                                                                                                                                                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_85_0~6356@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                               temp_85_1~6376@
                                                                                                                                                                                                                                                                                                                                                           ))))
                                                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_85_0~6356@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                              temp_85_1~6376@
                                                                                                                                                                                                                                                                                                                                                            ))
                                                                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                                                                             (= temp_86_0~6430@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                                                                                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.as_elem.?
                                                                                                                                                                                                                                                                                                                                                                   (I 13)
                                                                                                                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                                                                                                                 ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                   (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                             ))))))
                                                                                                                                                                                                                                                                                                                                                             (=>
                                                                                                                                                                                                                                                                                                                                                              (= temp_86_1~6492@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                 )
                                                                                                                                                                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.as_elem.?
                                                                                                                                                                                                                                                                                                                                                                    (I 13)
                                                                                                                                                                                                                                                                                                                                                                   )
                                                                                                                                                                                                                                                                                                                                                                  ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                                                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                        (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                            (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                           )
                                                                                                                                                                                                                                                                                                                                                                          ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                             )
                                                                                                                                                                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. b~4@)
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
                                                                                                                                                                                                                                                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_86_0~6430@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                   temp_86_1~6492@
                                                                                                                                                                                                                                                                                                                                                               ))))
                                                                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_86_0~6430@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                  temp_86_1~6492@
                                                                                                                                                                                                                                                                                                                                                                ))
                                                                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                                                                 (= temp_87_0~6534@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                 ))))
                                                                                                                                                                                                                                                                                                                                                                 (=>
                                                                                                                                                                                                                                                                                                                                                                  (= temp_87_1~6554@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                     )
                                                                                                                                                                                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                  ))))
                                                                                                                                                                                                                                                                                                                                                                  (and
                                                                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                                                                     %%location_label%%87
                                                                                                                                                                                                                                                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_87_0~6534@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                       temp_87_1~6554@
                                                                                                                                                                                                                                                                                                                                                                   ))))
                                                                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_87_0~6534@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                      temp_87_1~6554@
                                                                                                                                                                                                                                                                                                                                                                    ))
                                                                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                                                                     (= temp_88_0~6596@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                                                                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                     ))))
                                                                                                                                                                                                                                                                                                                                                                     (=>
                                                                                                                                                                                                                                                                                                                                                                      (= temp_88_1~6616@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                            (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                           )
                                                                                                                                                                                                                                                                                                                                                                          ) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                         )
                                                                                                                                                                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                      ))
                                                                                                                                                                                                                                                                                                                                                                      (and
                                                                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                                                                         %%location_label%%88
                                                                                                                                                                                                                                                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_88_0~6596@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                           temp_88_1~6616@
                                                                                                                                                                                                                                                                                                                                                                       ))))
                                                                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_88_0~6596@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                          temp_88_1~6616@
                                                                                                                                                                                                                                                                                                                                                                        ))
                                                                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                                                                         (= temp_89_0~6658@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                                                                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                         ))))
                                                                                                                                                                                                                                                                                                                                                                         (=>
                                                                                                                                                                                                                                                                                                                                                                          (= temp_89_1~6678@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                             )
                                                                                                                                                                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                          ))))
                                                                                                                                                                                                                                                                                                                                                                          (and
                                                                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                                                                                             %%location_label%%89
                                                                                                                                                                                                                                                                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_89_0~6658@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                               temp_89_1~6678@
                                                                                                                                                                                                                                                                                                                                                                           ))))
                                                                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_89_0~6658@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                              temp_89_1~6678@
                                                                                                                                                                                                                                                                                                                                                                            ))
                                                                                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                                                                                             (= temp_90_0~6710@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                b~4@
                                                                                                                                                                                                                                                                                                                                                                             )))
                                                                                                                                                                                                                                                                                                                                                                             (=>
                                                                                                                                                                                                                                                                                                                                                                              (= temp_90_1~6720@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                 b~4@
                                                                                                                                                                                                                                                                                                                                                                              )))
                                                                                                                                                                                                                                                                                                                                                                              (and
                                                                                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                                                                                 %%location_label%%90
                                                                                                                                                                                                                                                                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_90_0~6710@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                   temp_90_1~6720@
                                                                                                                                                                                                                                                                                                                                                                               ))))
                                                                                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_90_0~6710@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                  temp_90_1~6720@
                                                                                                                                                                                                                                                                                                                                                                                ))
                                                                                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                                                                                 (= temp_91_0~6762@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                                                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                 ))))
                                                                                                                                                                                                                                                                                                                                                                                 (=>
                                                                                                                                                                                                                                                                                                                                                                                  (= temp_91_1~6782@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                     (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                       (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                         c~6@
                                                                                                                                                                                                                                                                                                                                                                                  )))))))
                                                                                                                                                                                                                                                                                                                                                                                  (and
                                                                                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                                                                                     %%location_label%%91
                                                                                                                                                                                                                                                                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_91_0~6762@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                       temp_91_1~6782@
                                                                                                                                                                                                                                                                                                                                                                                   ))))
                                                                                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_91_0~6762@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                      temp_91_1~6782@
                                                                                                                                                                                                                                                                                                                                                                                    ))
                                                                                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                                                                                     (= temp_92_0~6834@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                                                                                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                           (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                                                                                                                                                                           ) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                                                                                                                                         ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                     ))))
                                                                                                                                                                                                                                                                                                                                                                                     (=>
                                                                                                                                                                                                                                                                                                                                                                                      (= temp_92_1~6864@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                         (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                           (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                               (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                 m~10@
                                                                                                                                                                                                                                                                                                                                                                                               ))
                                                                                                                                                                                                                                                                                                                                                                                              ) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                             )
                                                                                                                                                                                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                      ))))))
                                                                                                                                                                                                                                                                                                                                                                                      (and
                                                                                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                                                                                         %%location_label%%92
                                                                                                                                                                                                                                                                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_92_0~6834@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                           temp_92_1~6864@
                                                                                                                                                                                                                                                                                                                                                                                       ))))
                                                                                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_92_0~6834@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                          temp_92_1~6864@
                                                                                                                                                                                                                                                                                                                                                                                        ))
                                                                                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                                                                                         (= temp_93_0~6911@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                               (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                                                                                                                                                             ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                               (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                            )))
                                                                                                                                                                                                                                                                                                                                                                                           ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                         ))
                                                                                                                                                                                                                                                                                                                                                                                         (=>
                                                                                                                                                                                                                                                                                                                                                                                          (= temp_93_1~6941@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                               )
                                                                                                                                                                                                                                                                                                                                                                                              ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                                 )
                                                                                                                                                                                                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                             )))
                                                                                                                                                                                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                          ))
                                                                                                                                                                                                                                                                                                                                                                                          (and
                                                                                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                                                                                                             %%location_label%%93
                                                                                                                                                                                                                                                                                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_93_0~6911@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                               temp_93_1~6941@
                                                                                                                                                                                                                                                                                                                                                                                           ))))
                                                                                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_93_0~6911@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                              temp_93_1~6941@
                                                                                                                                                                                                                                                                                                                                                                                            ))
                                                                                                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                                                                                                             (= temp_94_0~6993@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                                                                                                                                                   ) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                                                                                                                                                 ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                                                                                                                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                             ))))
                                                                                                                                                                                                                                                                                                                                                                                             (=>
                                                                                                                                                                                                                                                                                                                                                                                              (= temp_94_1~7023@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                                        (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                       )
                                                                                                                                                                                                                                                                                                                                                                                                      ) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                                     )
                                                                                                                                                                                                                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                   )
                                                                                                                                                                                                                                                                                                                                                                                                  ) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                 )
                                                                                                                                                                                                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                              ))
                                                                                                                                                                                                                                                                                                                                                                                              (and
                                                                                                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                                                                                                 %%location_label%%94
                                                                                                                                                                                                                                                                                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_94_0~6993@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                   temp_94_1~7023@
                                                                                                                                                                                                                                                                                                                                                                                               ))))
                                                                                                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_94_0~6993@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                  temp_94_1~7023@
                                                                                                                                                                                                                                                                                                                                                                                                ))
                                                                                                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                                                                                                 (= temp_95_0~7070@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                                                                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                                       (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                 ))))))
                                                                                                                                                                                                                                                                                                                                                                                                 (=>
                                                                                                                                                                                                                                                                                                                                                                                                  (= temp_95_1~7120@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                                     )
                                                                                                                                                                                                                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.add_.?
                                                                                                                                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                            (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                                (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                               )
                                                                                                                                                                                                                                                                                                                                                                                                              ) (Poly%main!nl_basics.Elem. (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. a~2@)
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
                                                                                                                                                                                                                                                                                                                                                                                                     %%location_label%%95
                                                                                                                                                                                                                                                                                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_95_0~7070@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                       temp_95_1~7120@
                                                                                                                                                                                                                                                                                                                                                                                                   ))))
                                                                                                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_95_0~7070@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                      temp_95_1~7120@
                                                                                                                                                                                                                                                                                                                                                                                                    ))
                                                                                                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                                                                                                     (= temp_96_0~7162@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                                                                                                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                     ))))
                                                                                                                                                                                                                                                                                                                                                                                                     (=>
                                                                                                                                                                                                                                                                                                                                                                                                      (= temp_96_1~7182@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                         )
                                                                                                                                                                                                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                      ))))
                                                                                                                                                                                                                                                                                                                                                                                                      (and
                                                                                                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                                                                                                         %%location_label%%96
                                                                                                                                                                                                                                                                                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_96_0~7162@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                           temp_96_1~7182@
                                                                                                                                                                                                                                                                                                                                                                                                       ))))
                                                                                                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_96_0~7162@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                          temp_96_1~7182@
                                                                                                                                                                                                                                                                                                                                                                                                        ))
                                                                                                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                                                                                                         (= temp_97_0~7224@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                                                                                                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                         ))))
                                                                                                                                                                                                                                                                                                                                                                                                         (=>
                                                                                                                                                                                                                                                                                                                                                                                                          (= temp_97_1~7244@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                             )
                                                                                                                                                                                                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                          ))))
                                                                                                                                                                                                                                                                                                                                                                                                          (and
                                                                                                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                                                                                                                             %%location_label%%97
                                                                                                                                                                                                                                                                                                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_97_0~7224@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                               temp_97_1~7244@
                                                                                                                                                                                                                                                                                                                                                                                                           ))))
                                                                                                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_97_0~7224@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                              temp_97_1~7244@
                                                                                                                                                                                                                                                                                                                                                                                                            ))
                                                                                                                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                                                                                                                             (= temp_98_0~7286@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                                                                                                                                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                             ))))
                                                                                                                                                                                                                                                                                                                                                                                                             (=>
                                                                                                                                                                                                                                                                                                                                                                                                              (= temp_98_1~7306@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                                 )
                                                                                                                                                                                                                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                              ))))
                                                                                                                                                                                                                                                                                                                                                                                                              (and
                                                                                                                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                                                                                                                 %%location_label%%98
                                                                                                                                                                                                                                                                                                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_98_0~7286@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                   temp_98_1~7306@
                                                                                                                                                                                                                                                                                                                                                                                                               ))))
                                                                                                                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_98_0~7286@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                  temp_98_1~7306@
                                                                                                                                                                                                                                                                                                                                                                                                                ))
                                                                                                                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                                                                                                                 (= temp_99_0~7348@ (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                                                                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                                                                                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                                 ))))
                                                                                                                                                                                                                                                                                                                                                                                                                 (=>
                                                                                                                                                                                                                                                                                                                                                                                                                  (= temp_99_1~7368@ (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                                                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                                     )
                                                                                                                                                                                                                                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                                  ))))
                                                                                                                                                                                                                                                                                                                                                                                                                  (and
                                                                                                                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                                                                                                                     %%location_label%%99
                                                                                                                                                                                                                                                                                                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_99_0~7348@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                       temp_99_1~7368@
                                                                                                                                                                                                                                                                                                                                                                                                                   ))))
                                                                                                                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_99_0~7348@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                      temp_99_1~7368@
                                                                                                                                                                                                                                                                                                                                                                                                                    ))
                                                                                                                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                                                                                                                     (= temp_100_0~7410@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                                                                                                                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                                                     ))))
                                                                                                                                                                                                                                                                                                                                                                                                                     (=>
                                                                                                                                                                                                                                                                                                                                                                                                                      (= temp_100_1~7430@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                                         )
                                                                                                                                                                                                                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                                                      ))))
                                                                                                                                                                                                                                                                                                                                                                                                                      (and
                                                                                                                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                                                                                                                         %%location_label%%100
                                                                                                                                                                                                                                                                                                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_100_0~7410@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                           temp_100_1~7430@
                                                                                                                                                                                                                                                                                                                                                                                                                       ))))
                                                                                                                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_100_0~7410@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                          temp_100_1~7430@
                                                                                                                                                                                                                                                                                                                                                                                                                        ))
                                                                                                                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                                                                                                                         (= temp_101_0~7482@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                                                                                               (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                                            )))
                                                                                                                                                                                                                                                                                                                                                                                                                           ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                                                                                               (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                                                                                                                                                                                             ) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                                                         ))))
                                                                                                                                                                                                                                                                                                                                                                                                                         (=>
                                                                                                                                                                                                                                                                                                                                                                                                                          (= temp_101_1~7512@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                                                (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                                               )
                                                                                                                                                                                                                                                                                                                                                                                                                              ) (Poly%main!nl_basics.Elem. c~6@)
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
                                                                                                                                                                                                                                                                                                                                                                                                                             %%location_label%%101
                                                                                                                                                                                                                                                                                                                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_101_0~7482@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                               temp_101_1~7512@
                                                                                                                                                                                                                                                                                                                                                                                                                           ))))
                                                                                                                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_101_0~7482@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                              temp_101_1~7512@
                                                                                                                                                                                                                                                                                                                                                                                                                            ))
                                                                                                                                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                                                                                                                                             (= temp_102_0~7559@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                                                                                                                                                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                                                   (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                                                                                                                                                                                 ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                                             ))))
                                                                                                                                                                                                                                                                                                                                                                                                                             (=>
                                                                                                                                                                                                                                                                                                                                                                                                                              (= temp_102_1~7584@ (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                                                 )
                                                                                                                                                                                                                                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                                                    (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                                                   )
                                                                                                                                                                                                                                                                                                                                                                                                                                  ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                                              ))))
                                                                                                                                                                                                                                                                                                                                                                                                                              (and
                                                                                                                                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                 %%location_label%%102
                                                                                                                                                                                                                                                                                                                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_102_0~7559@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                                   temp_102_1~7584@
                                                                                                                                                                                                                                                                                                                                                                                                                               ))))
                                                                                                                                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_102_0~7559@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                                  temp_102_1~7584@
                                                                                                                                                                                                                                                                                                                                                                                                                                ))
                                                                                                                                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                 (= temp_103_0~7626@ (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                                                                                                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                                                                 ))))
                                                                                                                                                                                                                                                                                                                                                                                                                                 (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                  (= temp_103_1~7646@ (main!nl_basics.add_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                                                     )
                                                                                                                                                                                                                                                                                                                                                                                                                                    ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                                                                      (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                                                  ))))
                                                                                                                                                                                                                                                                                                                                                                                                                                  (and
                                                                                                                                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                     %%location_label%%103
                                                                                                                                                                                                                                                                                                                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_103_0~7626@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                                       temp_103_1~7646@
                                                                                                                                                                                                                                                                                                                                                                                                                                   ))))
                                                                                                                                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_103_0~7626@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                                      temp_103_1~7646@
                                                                                                                                                                                                                                                                                                                                                                                                                                    ))
                                                                                                                                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                     (= temp_104_0~7698@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                                                                                                           (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                                                        )))
                                                                                                                                                                                                                                                                                                                                                                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                                                           (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                                                     ))))))
                                                                                                                                                                                                                                                                                                                                                                                                                                     (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                      (= temp_104_1~7728@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                                         (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                                             c~6@
                                                                                                                                                                                                                                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                                                           )
                                                                                                                                                                                                                                                                                                                                                                                                                                          ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                                                            (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                                                      ))))))))
                                                                                                                                                                                                                                                                                                                                                                                                                                      (and
                                                                                                                                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                         %%location_label%%104
                                                                                                                                                                                                                                                                                                                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_104_0~7698@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                                           temp_104_1~7728@
                                                                                                                                                                                                                                                                                                                                                                                                                                       ))))
                                                                                                                                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_104_0~7698@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                                          temp_104_1~7728@
                                                                                                                                                                                                                                                                                                                                                                                                                                        ))
                                                                                                                                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                         (= temp_105_0~7765@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                                                                                                                                                                                                                           ) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                                                         ))
                                                                                                                                                                                                                                                                                                                                                                                                                                         (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                          (= temp_105_1~7780@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                                             (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                                               d~8@
                                                                                                                                                                                                                                                                                                                                                                                                                                          )))))
                                                                                                                                                                                                                                                                                                                                                                                                                                          (and
                                                                                                                                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                            (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                             %%location_label%%105
                                                                                                                                                                                                                                                                                                                                                                                                                                             (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_105_0~7765@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                                               temp_105_1~7780@
                                                                                                                                                                                                                                                                                                                                                                                                                                           ))))
                                                                                                                                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_105_0~7765@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                                              temp_105_1~7780@
                                                                                                                                                                                                                                                                                                                                                                                                                                            ))
                                                                                                                                                                                                                                                                                                                                                                                                                                            (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                             (= temp_106_0~7822@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                                                                                                                                                                                                               ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                 (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                                                             ))))
                                                                                                                                                                                                                                                                                                                                                                                                                                             (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                              (= temp_106_1~7842@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. b~4@) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                 )
                                                                                                                                                                                                                                                                                                                                                                                                                                                ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                                                              ))))
                                                                                                                                                                                                                                                                                                                                                                                                                                              (and
                                                                                                                                                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                                (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                                 %%location_label%%106
                                                                                                                                                                                                                                                                                                                                                                                                                                                 (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_106_0~7822@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                                                   temp_106_1~7842@
                                                                                                                                                                                                                                                                                                                                                                                                                                               ))))
                                                                                                                                                                                                                                                                                                                                                                                                                                               (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                                (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_106_0~7822@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                                                  temp_106_1~7842@
                                                                                                                                                                                                                                                                                                                                                                                                                                                ))
                                                                                                                                                                                                                                                                                                                                                                                                                                                (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                                 (= temp_107_0~7889@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                                                                                                                                                                                                   ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                     (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                       (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                 ))))))
                                                                                                                                                                                                                                                                                                                                                                                                                                                 (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                                  (= temp_107_1~7914@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                                                     (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                                                       (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                                                         (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. d~8@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                                                           m~10@
                                                                                                                                                                                                                                                                                                                                                                                                                                                  )))))))))
                                                                                                                                                                                                                                                                                                                                                                                                                                                  (and
                                                                                                                                                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                                    (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                                     %%location_label%%107
                                                                                                                                                                                                                                                                                                                                                                                                                                                     (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_107_0~7889@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                                                       temp_107_1~7914@
                                                                                                                                                                                                                                                                                                                                                                                                                                                   ))))
                                                                                                                                                                                                                                                                                                                                                                                                                                                   (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                                    (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_107_0~7889@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                                                      temp_107_1~7914@
                                                                                                                                                                                                                                                                                                                                                                                                                                                    ))
                                                                                                                                                                                                                                                                                                                                                                                                                                                    (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                                     (= temp_108_0~7961@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                           (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                                                                                                                                                                                                         ) (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                                                                                                                                                                                                                       ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                         (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                     ))))
                                                                                                                                                                                                                                                                                                                                                                                                                                                     (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                                      (= temp_108_1~7986@ (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. (main!nl_basics.mod_.?
                                                                                                                                                                                                                                                                                                                                                                                                                                                            (Poly%main!nl_basics.Elem. c~6@) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                         )))
                                                                                                                                                                                                                                                                                                                                                                                                                                                        ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                          (Poly%main!nl_basics.Elem. b~4@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                      ))))
                                                                                                                                                                                                                                                                                                                                                                                                                                                      (and
                                                                                                                                                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                                        (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                                         %%location_label%%108
                                                                                                                                                                                                                                                                                                                                                                                                                                                         (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_108_0~7961@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                                                           temp_108_1~7986@
                                                                                                                                                                                                                                                                                                                                                                                                                                                       ))))
                                                                                                                                                                                                                                                                                                                                                                                                                                                       (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                                        (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_108_0~7961@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                                                          temp_108_1~7986@
                                                                                                                                                                                                                                                                                                                                                                                                                                                        ))
                                                                                                                                                                                                                                                                                                                                                                                                                                                        (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                                         (= temp_109_0~8033@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.?
                                                                                                                                                                                                                                                                                                                                                                                                                                                             (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                               (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                                                                                                                                                                                                                             ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                               (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                            )))
                                                                                                                                                                                                                                                                                                                                                                                                                                                           ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                         ))
                                                                                                                                                                                                                                                                                                                                                                                                                                                         (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                                          (= temp_109_1~8068@ (main!nl_basics.mod_.? (Poly%main!nl_basics.Elem. (main!nl_basics.sub_.?
                                                                                                                                                                                                                                                                                                                                                                                                                                                              (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                               )))
                                                                                                                                                                                                                                                                                                                                                                                                                                                              ) (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. a~2@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                (Poly%main!nl_basics.Elem. (main!nl_basics.mul_.? (Poly%main!nl_basics.Elem. c~6@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                  (Poly%main!nl_basics.Elem. d~8@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                             )))))
                                                                                                                                                                                                                                                                                                                                                                                                                                                            ) (Poly%main!nl_basics.Elem. m~10@)
                                                                                                                                                                                                                                                                                                                                                                                                                                                          ))
                                                                                                                                                                                                                                                                                                                                                                                                                                                          (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                                           (ens%main!nl_basics.lemma_mul_properties_auto_1. 0)
                                                                                                                                                                                                                                                                                                                                                                                                                                                           (=>
                                                                                                                                                                                                                                                                                                                                                                                                                                                            %%location_label%%109
                                                                                                                                                                                                                                                                                                                                                                                                                                                            (main!nl_basics.eq_.? (Poly%main!nl_basics.Elem. temp_109_0~8033@) (Poly%main!nl_basics.Elem.
                                                                                                                                                                                                                                                                                                                                                                                                                                                              temp_109_1~8068@
 )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
 (get-info :version)
 (assert
  %%query%%
 )
 (set-option :rlimit 4294967295)
 (check-sat)
