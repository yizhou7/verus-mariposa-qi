(set-option :auto_config false)
(set-option :smt.mbqi false)
(set-option :smt.case_split 3)
(set-option :smt.qi.eager_threshold 100.0)
(set-option :smt.delay_units true)
(set-option :smt.arith.solver 2)
(set-option :smt.arith.nl false)
(set-option :timeout 5000)
(set-option :smt.arith.nl true)

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

;; Function-Def main::nlarith_0
;; mariposa_data/v_nl//7045881200950481896/nlqi_verus/src/main.rs:7:1: 36:40 (#0)
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
 (declare-const tmp%1@ Bool)
 (declare-const tmp%2@ Bool)
 (declare-const tmp%3@ Bool)
 (declare-const tmp%4@ Bool)
 (declare-const tmp%5@ Bool)
 (declare-const tmp%6@ Bool)
 (declare-const tmp%7@ Bool)
 (declare-const tmp%8@ Bool)
 (declare-const tmp%9@ Bool)
 (declare-const tmp%10@ Bool)
 (declare-const tmp%11@ Bool)
 (declare-const tmp%12@ Bool)
 (declare-const tmp%13@ Bool)
 (declare-const tmp%14@ Bool)
 (declare-const tmp%15@ Bool)
 (declare-const tmp%16@ Bool)
 (declare-const tmp%17@ Bool)
 (declare-const tmp%18@ Bool)
 (declare-const tmp%19@ Bool)
 (declare-const tmp%20@ Bool)
 (declare-const tmp%21@ Bool)
 (declare-const tmp%22@ Bool)
 (declare-const tmp%23@ Bool)
 (declare-const tmp%24@ Bool)
 (declare-const temp_0_0~305@ Int)
 (declare-const temp_0_1~370@ Int)
 (declare-const temp_1_0~462@ Int)
 (declare-const temp_1_1~539@ Int)
 (declare-const temp_2_0~619@ Int)
 (declare-const temp_2_1~716@ Int)
 (declare-const temp_3_0~796@ Int)
 (declare-const temp_3_1~861@ Int)
 (declare-const temp_4_0~925@ Int)
 (declare-const temp_4_1~974@ Int)
 (declare-const temp_5_0~1050@ Int)
 (declare-const temp_5_1~1111@ Int)
 (declare-const temp_6_0~1203@ Int)
 (declare-const temp_6_1~1280@ Int)
 (declare-const temp_7_0~1360@ Int)
 (declare-const temp_7_1~1425@ Int)
 (declare-const temp_8_0~1505@ Int)
 (declare-const temp_8_1~1602@ Int)
 (declare-const temp_9_0~1694@ Int)
 (declare-const temp_9_1~1771@ Int)
 (declare-const temp_10_0~1871@ Int)
 (declare-const temp_10_1~1956@ Int)
 (declare-const temp_11_0~2036@ Int)
 (declare-const temp_11_1~2101@ Int)
 (declare-const temp_12_0~2181@ Int)
 (declare-const temp_12_1~2246@ Int)
 (declare-const temp_13_0~2326@ Int)
 (declare-const temp_13_1~2391@ Int)
 (declare-const temp_14_0~2471@ Int)
 (declare-const temp_14_1~2536@ Int)
 (declare-const temp_15_0~2616@ Int)
 (declare-const temp_15_1~2681@ Int)
 (declare-const temp_16_0~2757@ Int)
 (declare-const temp_16_1~2818@ Int)
 (declare-const temp_17_0~2894@ Int)
 (declare-const temp_17_1~2955@ Int)
 (declare-const temp_18_0~3027@ Int)
 (declare-const temp_18_1~3084@ Int)
 (declare-const temp_19_0~3176@ Int)
 (declare-const temp_19_1~3253@ Int)
 (declare-const temp_20_0~3333@ Int)
 (declare-const temp_20_1~3398@ Int)
 (declare-const temp_21_0~3490@ Int)
 (declare-const temp_21_1~3567@ Int)
 (declare-const temp_22_0~3659@ Int)
 (declare-const temp_22_1~3736@ Int)
 (declare-const temp_23_0~3808@ Int)
 (declare-const temp_23_1~3865@ Int)
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
 (declare-const %%query%% Bool)
 (assert
  (=>
   %%query%%
   (not (=>
     (= temp_0_0~305@ (Mul (Mul (Mul (Mul a0~2@ a0~2@) (Mul a0~2@ d0~8@)) (Add (Add a0~2@ c0~6@)
         (Mul d0~8@ d0~8@)
        )
       ) (Mul (Mul (Mul c0~6@ d0~8@) (Sub d0~8@ c0~6@)) (Mul (Mul b0~4@ c0~6@) (Mul b0~4@ c0~6@)))
     ))
     (=>
      (= temp_0_1~370@ (Mul (Mul (Mul (Mul a0~2@ a0~2@) (Mul a0~2@ d0~8@)) (Add (Add a0~2@ c0~6@)
          (Mul d0~8@ d0~8@)
         )
        ) (Mul (Mul (Mul b0~4@ c0~6@) (Mul b0~4@ c0~6@)) (Mul (Mul c0~6@ d0~8@) (Sub d0~8@ c0~6@)))
      ))
      (=>
       (= tmp%1@ (= temp_0_0~305@ temp_0_1~370@))
       (and
        (=>
         %%location_label%%0
         tmp%1@
        )
        (=>
         tmp%1@
         (=>
          (= temp_1_0~462@ (Add (Add (Mul (Mul c1~14@ d1~16@) (Mul c1~14@ b1~12@)) (Mul (Mul a1~10@
               c1~14@
              ) (Mul d1~16@ 28)
             )
            ) (Add (Mul (Mul c1~14@ b1~12@) (Mul b1~12@ a1~10@)) (Mul (Mul d1~16@ c1~14@) (Mul b1~12@
               d1~16@
          )))))
          (=>
           (= temp_1_1~539@ (Add (Add (Mul (Mul c1~14@ d1~16@) (Mul c1~14@ b1~12@)) (Mul (Mul a1~10@
                c1~14@
               ) (Mul d1~16@ 28)
              )
             ) (Add (Mul (Mul b1~12@ a1~10@) (Mul c1~14@ b1~12@)) (Mul (Mul d1~16@ c1~14@) (Mul b1~12@
                d1~16@
           )))))
           (=>
            (= tmp%2@ (= temp_1_0~462@ temp_1_1~539@))
            (and
             (=>
              %%location_label%%1
              tmp%2@
             )
             (=>
              tmp%2@
              (=>
               (= temp_2_0~619@ (Mul (Mul (Mul (Mul d2~24@ b2~20@) (Mul c2~22@ c2~22@)) (Mul (Mul c2~22@
                    a2~18@
                   ) (Mul b2~20@ d2~24@)
                  )
                 ) (Add (Mul (Mul a2~18@ a2~18@) (Mul b2~20@ d2~24@)) (Sub (Sub c2~22@ c2~22@) (Mul a2~18@
                    b2~20@
               )))))
               (=>
                (= temp_2_1~716@ (Add (Mul (Mul (Mul (Mul d2~24@ b2~20@) (Mul c2~22@ c2~22@)) (Mul (Mul
                      c2~22@ a2~18@
                     ) (Mul b2~20@ d2~24@)
                    )
                   ) (Mul (Mul a2~18@ a2~18@) (Mul b2~20@ d2~24@))
                  ) (Mul (Mul (Mul (Mul d2~24@ b2~20@) (Mul c2~22@ c2~22@)) (Mul (Mul c2~22@ a2~18@) (
                      Mul b2~20@ d2~24@
                    ))
                   ) (Sub (Sub c2~22@ c2~22@) (Mul a2~18@ b2~20@))
                )))
                (=>
                 (= tmp%3@ (= temp_2_0~619@ temp_2_1~716@))
                 (and
                  (=>
                   %%location_label%%2
                   tmp%3@
                  )
                  (=>
                   tmp%3@
                   (=>
                    (= temp_3_0~796@ (Add (Mul (Mul (Mul a3~26@ b3~28@) (Mul d3~32@ d3~32@)) (Mul (Mul c3~30@
                         c3~30@
                        ) (Sub a3~26@ c3~30@)
                       )
                      ) (Add (Mul (Add b3~28@ a3~26@) (Sub b3~28@ d3~32@)) (Mul (Mul a3~26@ b3~28@) (Mul a3~26@
                         b3~28@
                    )))))
                    (=>
                     (= temp_3_1~861@ (Add (Mul (Mul (Mul a3~26@ b3~28@) (Mul d3~32@ d3~32@)) (Mul (Mul c3~30@
                          c3~30@
                         ) (Sub a3~26@ c3~30@)
                        )
                       ) (Add (Mul (Sub b3~28@ d3~32@) (Add b3~28@ a3~26@)) (Mul (Mul a3~26@ b3~28@) (Mul a3~26@
                          b3~28@
                     )))))
                     (=>
                      (= tmp%4@ (= temp_3_0~796@ temp_3_1~861@))
                      (and
                       (=>
                        %%location_label%%3
                        tmp%4@
                       )
                       (=>
                        tmp%4@
                        (=>
                         (= temp_4_0~925@ (Mul (Mul (Mul (Mul d4~40@ a4~34@) (Mul b4~36@ a4~34@)) b4~36@) (Mul
                            (Mul (Add b4~36@ d4~40@) a4~34@) (Mul (Mul b4~36@ b4~36@) (Mul d4~40@ d4~40@))
                         )))
                         (=>
                          (= temp_4_1~974@ (Mul (Mul (Mul (Mul d4~40@ a4~34@) (Mul b4~36@ a4~34@)) b4~36@) (Mul
                             (Add b4~36@ d4~40@) (Mul a4~34@ (Mul (Mul b4~36@ b4~36@) (Mul d4~40@ d4~40@)))
                          )))
                          (=>
                           (= tmp%5@ (= temp_4_0~925@ temp_4_1~974@))
                           (and
                            (=>
                             %%location_label%%4
                             tmp%5@
                            )
                            (=>
                             tmp%5@
                             (=>
                              (= temp_5_0~1050@ (Mul (Add (Mul (Mul c5~46@ d5~48@) (Mul a5~42@ c5~46@)) (Add c5~46@
                                  (Add d5~48@ d5~48@)
                                 )
                                ) (Mul (Mul (Mul c5~46@ c5~46@) (Mul b5~44@ a5~42@)) (Mul (Add b5~44@ c5~46@) (Add c5~46@
                                   a5~42@
                              )))))
                              (=>
                               (= temp_5_1~1111@ (Mul (Add (Mul (Mul c5~46@ d5~48@) (Mul c5~46@ a5~42@)) (Add c5~46@
                                   (Add d5~48@ d5~48@)
                                  )
                                 ) (Mul (Mul (Mul c5~46@ c5~46@) (Mul b5~44@ a5~42@)) (Mul (Add b5~44@ c5~46@) (Add c5~46@
                                    a5~42@
                               )))))
                               (=>
                                (= tmp%6@ (= temp_5_0~1050@ temp_5_1~1111@))
                                (and
                                 (=>
                                  %%location_label%%5
                                  tmp%6@
                                 )
                                 (=>
                                  tmp%6@
                                  (=>
                                   (= temp_6_0~1203@ (Sub (Sub (Mul (Add c6~54@ d6~56@) (Sub c6~54@ b6~52@)) (Mul (Mul b6~52@
                                        c6~54@
                                       ) (Mul d6~56@ b6~52@)
                                      )
                                     ) (Mul (Mul (Mul c6~54@ d6~56@) (Mul c6~54@ 6)) (Mul (Mul a6~50@ d6~56@) (Sub b6~52@
                                        c6~54@
                                   )))))
                                   (=>
                                    (= temp_6_1~1280@ (Sub (Sub (Mul (Add c6~54@ d6~56@) (Sub c6~54@ b6~52@)) (Mul (Mul b6~52@
                                         c6~54@
                                        ) (Mul d6~56@ b6~52@)
                                       )
                                      ) (Mul (Mul (Mul (Mul c6~54@ d6~56@) c6~54@) 6) (Mul (Mul a6~50@ d6~56@) (Sub b6~52@
                                         c6~54@
                                    )))))
                                    (=>
                                     (= tmp%7@ (= temp_6_0~1203@ temp_6_1~1280@))
                                     (and
                                      (=>
                                       %%location_label%%6
                                       tmp%7@
                                      )
                                      (=>
                                       tmp%7@
                                       (=>
                                        (= temp_7_0~1360@ (Mul (Mul (Mul (Add c7~62@ c7~62@) (Mul d7~64@ b7~60@)) (Mul (Mul d7~64@
                                             d7~64@
                                            ) (Mul b7~60@ b7~60@)
                                           )
                                          ) (Mul (Mul (Mul d7~64@ b7~60@) (Mul a7~58@ a7~58@)) (Mul (Mul a7~58@ d7~64@) (Mul c7~62@
                                             a7~58@
                                        )))))
                                        (=>
                                         (= temp_7_1~1425@ (Mul (Mul (Mul (Add c7~62@ c7~62@) (Mul d7~64@ b7~60@)) (Mul (Mul d7~64@
                                              d7~64@
                                             ) (Mul b7~60@ b7~60@)
                                            )
                                           ) (Mul (Mul (Mul d7~64@ b7~60@) (Mul a7~58@ a7~58@)) (Mul (Mul d7~64@ a7~58@) (Mul c7~62@
                                              a7~58@
                                         )))))
                                         (=>
                                          (= tmp%8@ (= temp_7_0~1360@ temp_7_1~1425@))
                                          (and
                                           (=>
                                            %%location_label%%7
                                            tmp%8@
                                           )
                                           (=>
                                            tmp%8@
                                            (=>
                                             (= temp_8_0~1505@ (Mul (Mul (Mul (Mul d8~72@ b8~68@) (Sub c8~70@ d8~72@)) (Mul (Mul b8~68@
                                                  a8~66@
                                                 ) (Sub a8~66@ b8~68@)
                                                )
                                               ) (Add (Mul (Mul d8~72@ c8~70@) (Add c8~70@ b8~68@)) (Mul (Mul c8~70@ d8~72@) (Sub b8~68@
                                                  a8~66@
                                             )))))
                                             (=>
                                              (= temp_8_1~1602@ (Add (Mul (Mul (Mul (Mul d8~72@ b8~68@) (Sub c8~70@ d8~72@)) (Mul (Mul
                                                    b8~68@ a8~66@
                                                   ) (Sub a8~66@ b8~68@)
                                                  )
                                                 ) (Mul (Mul d8~72@ c8~70@) (Add c8~70@ b8~68@))
                                                ) (Mul (Mul (Mul (Mul d8~72@ b8~68@) (Sub c8~70@ d8~72@)) (Mul (Mul b8~68@ a8~66@) (
                                                    Sub a8~66@ b8~68@
                                                  ))
                                                 ) (Mul (Mul c8~70@ d8~72@) (Sub b8~68@ a8~66@))
                                              )))
                                              (=>
                                               (= tmp%9@ (= temp_8_0~1505@ temp_8_1~1602@))
                                               (and
                                                (=>
                                                 %%location_label%%8
                                                 tmp%9@
                                                )
                                                (=>
                                                 tmp%9@
                                                 (=>
                                                  (= temp_9_0~1694@ (Mul (Mul (Mul (Mul a9~74@ c9~78@) (Mul a9~74@ a9~74@)) (Add (Add c9~78@
                                                       c9~78@
                                                      ) (Mul b9~76@ d9~80@)
                                                     )
                                                    ) (Mul (Mul (Mul 84 a9~74@) (Mul a9~74@ d9~80@)) (Mul (Mul c9~78@ b9~76@) (Mul d9~80@
                                                       a9~74@
                                                  )))))
                                                  (=>
                                                   (= temp_9_1~1771@ (Mul (Mul (Mul (Mul a9~74@ c9~78@) (Mul a9~74@ a9~74@)) (Add (Add c9~78@
                                                        c9~78@
                                                       ) (Mul b9~76@ d9~80@)
                                                      )
                                                     ) (Mul (Mul (Mul 84 a9~74@) (Mul a9~74@ d9~80@)) (Mul (Mul b9~76@ c9~78@) (Mul d9~80@
                                                        a9~74@
                                                   )))))
                                                   (=>
                                                    (= tmp%10@ (= temp_9_0~1694@ temp_9_1~1771@))
                                                    (and
                                                     (=>
                                                      %%location_label%%9
                                                      tmp%10@
                                                     )
                                                     (=>
                                                      tmp%10@
                                                      (=>
                                                       (= temp_10_0~1871@ (Mul (Add (Mul (Sub d10~88@ b10~84@) d10~88@) (Mul (Mul d10~88@ c10~86@)
                                                           (Mul c10~86@ a10~82@)
                                                          )
                                                         ) (Sub (Mul (Mul b10~84@ a10~82@) (Sub a10~82@ d10~88@)) (Add (Mul d10~88@ a10~82@)
                                                           (Mul 97 96)
                                                       ))))
                                                       (=>
                                                        (= temp_10_1~1956@ (Mul (Add (Mul (Sub d10~88@ b10~84@) d10~88@) (Mul (Mul c10~86@ a10~82@)
                                                            (Mul d10~88@ c10~86@)
                                                           )
                                                          ) (Sub (Mul (Mul b10~84@ a10~82@) (Sub a10~82@ d10~88@)) (Add (Mul d10~88@ a10~82@)
                                                            (Mul 97 96)
                                                        ))))
                                                        (=>
                                                         (= tmp%11@ (= temp_10_0~1871@ temp_10_1~1956@))
                                                         (and
                                                          (=>
                                                           %%location_label%%10
                                                           tmp%11@
                                                          )
                                                          (=>
                                                           tmp%11@
                                                           (=>
                                                            (= temp_11_0~2036@ (Mul (Mul (Mul (Mul a11~90@ b11~92@) (Mul d11~96@ b11~92@)) (Mul (
                                                                 Mul d11~96@ b11~92@
                                                                ) (Mul d11~96@ a11~90@)
                                                               )
                                                              ) (Mul (Mul (Mul d11~96@ c11~94@) (Mul a11~90@ d11~96@)) (Mul (Mul d11~96@ c11~94@)
                                                                (Mul a11~90@ a11~90@)
                                                            ))))
                                                            (=>
                                                             (= temp_11_1~2101@ (Mul (Mul (Mul (Mul a11~90@ b11~92@) (Mul d11~96@ b11~92@)) (Mul (
                                                                  Mul d11~96@ b11~92@
                                                                 ) (Mul a11~90@ d11~96@)
                                                                )
                                                               ) (Mul (Mul (Mul d11~96@ c11~94@) (Mul a11~90@ d11~96@)) (Mul (Mul d11~96@ c11~94@)
                                                                 (Mul a11~90@ a11~90@)
                                                             ))))
                                                             (=>
                                                              (= tmp%12@ (= temp_11_0~2036@ temp_11_1~2101@))
                                                              (and
                                                               (=>
                                                                %%location_label%%11
                                                                tmp%12@
                                                               )
                                                               (=>
                                                                tmp%12@
                                                                (=>
                                                                 (= temp_12_0~2181@ (Add (Mul (Mul (Mul c12~102@ a12~98@) (Mul b12~100@ a12~98@)) (Mul
                                                                     (Mul a12~98@ c12~102@) (Add d12~104@ d12~104@)
                                                                    )
                                                                   ) (Sub (Mul (Add a12~98@ b12~100@) (Mul a12~98@ b12~100@)) (Mul (Sub c12~102@ c12~102@)
                                                                     (Mul c12~102@ c12~102@)
                                                                 ))))
                                                                 (=>
                                                                  (= temp_12_1~2246@ (Add (Mul (Mul c12~102@ (Mul a12~98@ (Mul b12~100@ a12~98@))) (Mul
                                                                      (Mul a12~98@ c12~102@) (Add d12~104@ d12~104@)
                                                                     )
                                                                    ) (Sub (Mul (Add a12~98@ b12~100@) (Mul a12~98@ b12~100@)) (Mul (Sub c12~102@ c12~102@)
                                                                      (Mul c12~102@ c12~102@)
                                                                  ))))
                                                                  (=>
                                                                   (= tmp%13@ (= temp_12_0~2181@ temp_12_1~2246@))
                                                                   (and
                                                                    (=>
                                                                     %%location_label%%12
                                                                     tmp%13@
                                                                    )
                                                                    (=>
                                                                     tmp%13@
                                                                     (=>
                                                                      (= temp_13_0~2326@ (Mul (Mul (Mul (Mul c13~110@ d13~112@) (Mul a13~106@ a13~106@)) (
                                                                          Mul (Mul d13~112@ c13~110@) (Mul d13~112@ d13~112@)
                                                                         )
                                                                        ) (Mul (Mul (Mul b13~108@ b13~108@) (Mul a13~106@ b13~108@)) (Add (Mul c13~110@ a13~106@)
                                                                          (Mul c13~110@ d13~112@)
                                                                      ))))
                                                                      (=>
                                                                       (= temp_13_1~2391@ (Mul (Mul (Mul (Mul c13~110@ d13~112@) (Mul a13~106@ a13~106@)) (
                                                                           Mul (Mul d13~112@ c13~110@) (Mul d13~112@ d13~112@)
                                                                          )
                                                                         ) (Mul (Add (Mul c13~110@ a13~106@) (Mul c13~110@ d13~112@)) (Mul (Mul b13~108@ b13~108@)
                                                                           (Mul a13~106@ b13~108@)
                                                                       ))))
                                                                       (=>
                                                                        (= tmp%14@ (= temp_13_0~2326@ temp_13_1~2391@))
                                                                        (and
                                                                         (=>
                                                                          %%location_label%%13
                                                                          tmp%14@
                                                                         )
                                                                         (=>
                                                                          tmp%14@
                                                                          (=>
                                                                           (= temp_14_0~2471@ (Sub (Mul a14~114@ (Mul (Mul b14~116@ a14~114@) (Mul d14~120@ 9)))
                                                                             (Mul (Mul (Mul a14~114@ a14~114@) (Sub c14~118@ c14~118@)) (Mul (Mul d14~120@ a14~114@)
                                                                               (Mul c14~118@ a14~114@)
                                                                           ))))
                                                                           (=>
                                                                            (= temp_14_1~2536@ (Sub (Mul a14~114@ (Mul (Mul b14~116@ a14~114@) (Mul d14~120@ 9)))
                                                                              (Mul (Mul (Mul a14~114@ a14~114@) (Sub c14~118@ c14~118@)) (Mul (Mul c14~118@ a14~114@)
                                                                                (Mul d14~120@ a14~114@)
                                                                            ))))
                                                                            (=>
                                                                             (= tmp%15@ (= temp_14_0~2471@ temp_14_1~2536@))
                                                                             (and
                                                                              (=>
                                                                               %%location_label%%14
                                                                               tmp%15@
                                                                              )
                                                                              (=>
                                                                               tmp%15@
                                                                               (=>
                                                                                (= temp_15_0~2616@ (Mul (Mul (Mul (Mul d15~128@ b15~124@) (Sub b15~124@ d15~128@)) (
                                                                                    Mul a15~122@ (Mul 16 a15~122@)
                                                                                   )
                                                                                  ) (Mul (Mul c15~126@ (Sub d15~128@ a15~122@)) (Mul (Mul d15~128@ a15~122@) c15~126@))
                                                                                ))
                                                                                (=>
                                                                                 (= temp_15_1~2681@ (Mul (Mul (Mul (Mul d15~128@ b15~124@) (Sub b15~124@ d15~128@)) (
                                                                                     Mul a15~122@ (Mul 16 a15~122@)
                                                                                    )
                                                                                   ) (Mul (Mul (Mul c15~126@ (Sub d15~128@ a15~122@)) (Mul d15~128@ a15~122@)) c15~126@)
                                                                                 ))
                                                                                 (=>
                                                                                  (= tmp%16@ (= temp_15_0~2616@ temp_15_1~2681@))
                                                                                  (and
                                                                                   (=>
                                                                                    %%location_label%%15
                                                                                    tmp%16@
                                                                                   )
                                                                                   (=>
                                                                                    tmp%16@
                                                                                    (=>
                                                                                     (= temp_16_0~2757@ (Mul (Mul (Mul d16~136@ (Mul c16~134@ c16~134@)) (Mul (Add d16~136@
                                                                                          b16~132@
                                                                                         ) (Mul a16~130@ b16~132@)
                                                                                        )
                                                                                       ) (Mul (Mul (Mul d16~136@ b16~132@) (Sub a16~130@ c16~134@)) (Mul (Mul a16~130@ b16~132@)
                                                                                         (Mul d16~136@ c16~134@)
                                                                                     ))))
                                                                                     (=>
                                                                                      (= temp_16_1~2818@ (Mul (Mul (Mul d16~136@ (Mul c16~134@ c16~134@)) (Mul (Add d16~136@
                                                                                           b16~132@
                                                                                          ) (Mul a16~130@ b16~132@)
                                                                                         )
                                                                                        ) (Mul (Mul (Mul b16~132@ d16~136@) (Sub a16~130@ c16~134@)) (Mul (Mul a16~130@ b16~132@)
                                                                                          (Mul d16~136@ c16~134@)
                                                                                      ))))
                                                                                      (=>
                                                                                       (= tmp%17@ (= temp_16_0~2757@ temp_16_1~2818@))
                                                                                       (and
                                                                                        (=>
                                                                                         %%location_label%%16
                                                                                         tmp%17@
                                                                                        )
                                                                                        (=>
                                                                                         tmp%17@
                                                                                         (=>
                                                                                          (= temp_17_0~2894@ (Mul (Mul (Mul (Mul c17~142@ d17~144@) (Mul a17~138@ d17~144@)) (
                                                                                              Sub (Mul c17~142@ b17~140@) (Add c17~142@ a17~138@)
                                                                                             )
                                                                                            ) (Mul (Mul (Mul c17~142@ b17~140@) (Mul d17~144@ d17~144@)) (Mul b17~140@ (Mul d17~144@
                                                                                               a17~138@
                                                                                          )))))
                                                                                          (=>
                                                                                           (= temp_17_1~2955@ (Mul (Mul (Mul c17~142@ d17~144@) (Mul a17~138@ d17~144@)) (Mul (
                                                                                               Sub (Mul c17~142@ b17~140@) (Add c17~142@ a17~138@)
                                                                                              ) (Mul (Mul (Mul c17~142@ b17~140@) (Mul d17~144@ d17~144@)) (Mul b17~140@ (Mul d17~144@
                                                                                                 a17~138@
                                                                                           ))))))
                                                                                           (=>
                                                                                            (= tmp%18@ (= temp_17_0~2894@ temp_17_1~2955@))
                                                                                            (and
                                                                                             (=>
                                                                                              %%location_label%%17
                                                                                              tmp%18@
                                                                                             )
                                                                                             (=>
                                                                                              tmp%18@
                                                                                              (=>
                                                                                               (= temp_18_0~3027@ (Mul (Add (Sub (Add b18~148@ b18~148@) (Mul c18~150@ c18~150@)) (
                                                                                                   Mul (Add d18~152@ d18~152@) (Sub c18~150@ d18~152@)
                                                                                                  )
                                                                                                 ) (Mul (Mul (Sub b18~148@ b18~148@) b18~148@) (Mul (Mul b18~148@ d18~152@) b18~148@))
                                                                                               ))
                                                                                               (=>
                                                                                                (= temp_18_1~3084@ (Mul (Add (Sub (Add b18~148@ b18~148@) (Mul c18~150@ c18~150@)) (
                                                                                                    Mul (Add d18~152@ d18~152@) (Sub c18~150@ d18~152@)
                                                                                                   )
                                                                                                  ) (Mul (Mul b18~148@ (Sub b18~148@ b18~148@)) (Mul (Mul b18~148@ d18~152@) b18~148@))
                                                                                                ))
                                                                                                (=>
                                                                                                 (= tmp%19@ (= temp_18_0~3027@ temp_18_1~3084@))
                                                                                                 (and
                                                                                                  (=>
                                                                                                   %%location_label%%18
                                                                                                   tmp%19@
                                                                                                  )
                                                                                                  (=>
                                                                                                   tmp%19@
                                                                                                   (=>
                                                                                                    (= temp_19_0~3176@ (Sub (Mul (Sub (Add 24 b19~156@) (Mul c19~158@ b19~156@)) (Mul (Add
                                                                                                         a19~154@ a19~154@
                                                                                                        ) (Mul b19~156@ d19~160@)
                                                                                                       )
                                                                                                      ) (Mul (Mul (Sub c19~158@ b19~156@) (Mul a19~154@ a19~154@)) (Mul (Mul d19~160@ a19~154@)
                                                                                                        (Mul a19~154@ c19~158@)
                                                                                                    ))))
                                                                                                    (=>
                                                                                                     (= temp_19_1~3253@ (Sub (Mul (Sub (Add 24 b19~156@) (Mul c19~158@ b19~156@)) (Mul (Add
                                                                                                          a19~154@ a19~154@
                                                                                                         ) (Mul b19~156@ d19~160@)
                                                                                                        )
                                                                                                       ) (Mul (Mul (Mul (Sub c19~158@ b19~156@) (Mul a19~154@ a19~154@)) (Mul d19~160@ a19~154@))
                                                                                                        (Mul a19~154@ c19~158@)
                                                                                                     )))
                                                                                                     (=>
                                                                                                      (= tmp%20@ (= temp_19_0~3176@ temp_19_1~3253@))
                                                                                                      (and
                                                                                                       (=>
                                                                                                        %%location_label%%19
                                                                                                        tmp%20@
                                                                                                       )
                                                                                                       (=>
                                                                                                        tmp%20@
                                                                                                        (=>
                                                                                                         (= temp_20_0~3333@ (Add (Mul (Mul (Mul d20~168@ b20~164@) (Mul d20~168@ b20~164@)) (
                                                                                                             Mul (Mul a20~162@ c20~166@) (Mul b20~164@ c20~166@)
                                                                                                            )
                                                                                                           ) (Mul (Add (Mul b20~164@ b20~164@) (Sub d20~168@ a20~162@)) (Mul (Sub d20~168@ d20~168@)
                                                                                                             (Mul b20~164@ d20~168@)
                                                                                                         ))))
                                                                                                         (=>
                                                                                                          (= temp_20_1~3398@ (Add (Mul (Mul (Mul d20~168@ b20~164@) (Mul d20~168@ b20~164@)) (
                                                                                                              Mul (Mul c20~166@ a20~162@) (Mul b20~164@ c20~166@)
                                                                                                             )
                                                                                                            ) (Mul (Add (Mul b20~164@ b20~164@) (Sub d20~168@ a20~162@)) (Mul (Sub d20~168@ d20~168@)
                                                                                                              (Mul b20~164@ d20~168@)
                                                                                                          ))))
                                                                                                          (=>
                                                                                                           (= tmp%21@ (= temp_20_0~3333@ temp_20_1~3398@))
                                                                                                           (and
                                                                                                            (=>
                                                                                                             %%location_label%%20
                                                                                                             tmp%21@
                                                                                                            )
                                                                                                            (=>
                                                                                                             tmp%21@
                                                                                                             (=>
                                                                                                              (= temp_21_0~3490@ (Add (Mul (Mul (Add b21~172@ d21~176@) (Mul c21~174@ a21~170@)) (
                                                                                                                  Mul (Sub c21~174@ b21~172@) (Mul b21~172@ c21~174@)
                                                                                                                 )
                                                                                                                ) (Mul (Mul (Mul c21~174@ d21~176@) (Mul d21~176@ a21~170@)) (Mul (Mul c21~174@ c21~174@)
                                                                                                                  (Mul a21~170@ 2)
                                                                                                              ))))
                                                                                                              (=>
                                                                                                               (= temp_21_1~3567@ (Add (Mul (Mul (Add b21~172@ d21~176@) (Mul c21~174@ a21~170@)) (
                                                                                                                   Mul (Sub c21~174@ b21~172@) (Mul b21~172@ c21~174@)
                                                                                                                  )
                                                                                                                 ) (Mul (Mul (Mul d21~176@ a21~170@) (Mul c21~174@ d21~176@)) (Mul (Mul c21~174@ c21~174@)
                                                                                                                   (Mul a21~170@ 2)
                                                                                                               ))))
                                                                                                               (=>
                                                                                                                (= tmp%22@ (= temp_21_0~3490@ temp_21_1~3567@))
                                                                                                                (and
                                                                                                                 (=>
                                                                                                                  %%location_label%%21
                                                                                                                  tmp%22@
                                                                                                                 )
                                                                                                                 (=>
                                                                                                                  tmp%22@
                                                                                                                  (=>
                                                                                                                   (= temp_22_0~3659@ (Mul (Mul (Mul (Mul c22~182@ a22~178@) (Mul a22~178@ c22~182@)) (
                                                                                                                       Mul (Mul 62 d22~184@) (Sub a22~178@ d22~184@)
                                                                                                                      )
                                                                                                                     ) (Add (Sub (Mul a22~178@ c22~182@) (Sub b22~180@ c22~182@)) (Mul (Mul d22~184@ b22~180@)
                                                                                                                       (Mul d22~184@ d22~184@)
                                                                                                                   ))))
                                                                                                                   (=>
                                                                                                                    (= temp_22_1~3736@ (Mul (Mul (Mul (Mul c22~182@ a22~178@) (Mul c22~182@ a22~178@)) (
                                                                                                                        Mul (Mul 62 d22~184@) (Sub a22~178@ d22~184@)
                                                                                                                       )
                                                                                                                      ) (Add (Sub (Mul a22~178@ c22~182@) (Sub b22~180@ c22~182@)) (Mul (Mul d22~184@ b22~180@)
                                                                                                                        (Mul d22~184@ d22~184@)
                                                                                                                    ))))
                                                                                                                    (=>
                                                                                                                     (= tmp%23@ (= temp_22_0~3659@ temp_22_1~3736@))
                                                                                                                     (and
                                                                                                                      (=>
                                                                                                                       %%location_label%%22
                                                                                                                       tmp%23@
                                                                                                                      )
                                                                                                                      (=>
                                                                                                                       tmp%23@
                                                                                                                       (=>
                                                                                                                        (= temp_23_0~3808@ (Mul (Mul (Mul (Mul c23~190@ b23~188@) (Mul c23~190@ d23~192@)) (
                                                                                                                            Mul (Mul b23~188@ c23~190@) a23~186@
                                                                                                                           )
                                                                                                                          ) (Mul (Mul (Mul a23~186@ a23~186@) d23~192@) (Mul (Mul a23~186@ d23~192@) (Mul c23~190@
                                                                                                                             c23~190@
                                                                                                                        )))))
                                                                                                                        (=>
                                                                                                                         (= temp_23_1~3865@ (Mul (Mul (Mul (Mul c23~190@ b23~188@) (Mul c23~190@ d23~192@)) (
                                                                                                                             Mul b23~188@ (Mul c23~190@ a23~186@)
                                                                                                                            )
                                                                                                                           ) (Mul (Mul (Mul a23~186@ a23~186@) d23~192@) (Mul (Mul a23~186@ d23~192@) (Mul c23~190@
                                                                                                                              c23~190@
                                                                                                                         )))))
                                                                                                                         (=>
                                                                                                                          (= tmp%24@ (= temp_23_0~3808@ temp_23_1~3865@))
                                                                                                                          (=>
                                                                                                                           %%location_label%%23
                                                                                                                           tmp%24@
 ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
 (get-info :version)
 (assert
  %%query%%
 )
 (set-option :rlimit 4294967295)
 (check-sat)
 (set-option :rlimit 0)
(pop)
