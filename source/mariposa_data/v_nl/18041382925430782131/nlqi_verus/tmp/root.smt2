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
;; mariposa_data/v_nl//18041382925430782131/nlqi_verus/src/main.rs:7:1: 36:40 (#0)
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
 (declare-const temp_0_0~305@ Int)
 (declare-const temp_0_1~370@ Int)
 (declare-const temp_1_0~450@ Int)
 (declare-const temp_1_1~547@ Int)
 (declare-const temp_2_0~627@ Int)
 (declare-const temp_2_1~688@ Int)
 (declare-const temp_3_0~740@ Int)
 (declare-const temp_3_1~777@ Int)
 (declare-const temp_4_0~829@ Int)
 (declare-const temp_4_1~874@ Int)
 (declare-const temp_5_0~938@ Int)
 (declare-const temp_5_1~1007@ Int)
 (declare-const temp_6_0~1099@ Int)
 (declare-const temp_6_1~1176@ Int)
 (declare-const temp_7_0~1264@ Int)
 (declare-const temp_7_1~1365@ Int)
 (declare-const temp_8_0~1453@ Int)
 (declare-const temp_8_1~1526@ Int)
 (declare-const temp_9_0~1606@ Int)
 (declare-const temp_9_1~1671@ Int)
 (declare-const temp_10_0~1747@ Int)
 (declare-const temp_10_1~1808@ Int)
 (declare-const temp_11_0~1872@ Int)
 (declare-const temp_11_1~1921@ Int)
 (declare-const temp_12_0~1989@ Int)
 (declare-const temp_12_1~2042@ Int)
 (declare-const temp_13_0~2094@ Int)
 (declare-const temp_13_1~2147@ Int)
 (declare-const temp_14_0~2235@ Int)
 (declare-const temp_14_1~2308@ Int)
 (declare-const temp_15_0~2388@ Int)
 (declare-const temp_15_1~2453@ Int)
 (declare-const temp_16_0~2541@ Int)
 (declare-const temp_16_1~2614@ Int)
 (declare-const temp_17_0~2706@ Int)
 (declare-const temp_17_1~2783@ Int)
 (declare-const temp_18_0~2863@ Int)
 (declare-const temp_18_1~2928@ Int)
 (declare-const temp_19_0~2996@ Int)
 (declare-const temp_19_1~3049@ Int)
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
 (declare-const %%query%% Bool)
 (assert
  (=>
   %%query%%
   (not (=>
     (= temp_0_0~305@ (Mul (Mul (Sub (Mul c0~6@ d0~8@) (Add a0~2@ d0~8@)) (Add (Mul d0~8@ b0~4@)
         (Mul d0~8@ c0~6@)
        )
       ) (Mul (Mul (Mul c0~6@ b0~4@) (Mul a0~2@ c0~6@)) (Mul (Add b0~4@ b0~4@) (Mul d0~8@ a0~2@)))
     ))
     (=>
      (= temp_0_1~370@ (Mul (Mul (Sub (Mul c0~6@ d0~8@) (Add a0~2@ d0~8@)) (Add (Mul d0~8@ b0~4@)
          (Mul d0~8@ c0~6@)
         )
        ) (Mul (Mul (Mul c0~6@ b0~4@) (Mul a0~2@ c0~6@)) (Mul (Add b0~4@ b0~4@) (Mul a0~2@ d0~8@)))
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
          (= temp_1_0~450@ (Mul (Sub (Mul (Add a1~10@ b1~12@) (Mul c1~14@ a1~10@)) (Mul (Sub b1~12@
               c1~14@
              ) (Mul c1~14@ d1~16@)
             )
            ) (Mul (Mul (Mul b1~12@ d1~16@) (Mul d1~16@ b1~12@)) (Mul (Mul b1~12@ c1~14@) (Mul c1~14@
               a1~10@
          )))))
          (=>
           (= temp_1_1~547@ (Sub (Mul (Mul (Add a1~10@ b1~12@) (Mul c1~14@ a1~10@)) (Mul (Mul (Mul
                 b1~12@ d1~16@
                ) (Mul d1~16@ b1~12@)
               ) (Mul (Mul b1~12@ c1~14@) (Mul c1~14@ a1~10@))
              )
             ) (Mul (Mul (Sub b1~12@ c1~14@) (Mul c1~14@ d1~16@)) (Mul (Mul (Mul b1~12@ d1~16@) (
                 Mul d1~16@ b1~12@
                )
               ) (Mul (Mul b1~12@ c1~14@) (Mul c1~14@ a1~10@))
           ))))
           (=>
            (= tmp%2@ (= temp_1_0~450@ temp_1_1~547@))
            (and
             (=>
              %%location_label%%1
              tmp%2@
             )
             (=>
              tmp%2@
              (=>
               (= temp_2_0~627@ (Sub (Mul (Mul (Add a2~18@ b2~20@) (Add a2~18@ c2~22@)) (Mul (Mul b2~20@
                    a2~18@
                   ) (Mul b2~20@ b2~20@)
                  )
                 ) (Mul (Add (Mul c2~22@ a2~18@) (Mul b2~20@ a2~18@)) (Mul (Mul b2~20@ a2~18@) (Add b2~20@
                    b2~20@
               )))))
               (=>
                (= temp_2_1~688@ (Sub (Mul (Mul (Add a2~18@ b2~20@) (Add a2~18@ c2~22@)) (Mul (Mul b2~20@
                     a2~18@
                    ) (Mul b2~20@ b2~20@)
                   )
                  ) (Mul (Mul (Add c2~22@ b2~20@) a2~18@) (Mul (Mul b2~20@ a2~18@) (Add b2~20@ b2~20@)))
                ))
                (=>
                 (= tmp%3@ (= temp_2_0~627@ temp_2_1~688@))
                 (and
                  (=>
                   %%location_label%%2
                   tmp%3@
                  )
                  (=>
                   tmp%3@
                   (=>
                    (= temp_3_0~740@ (Mul (Mul (Mul (Mul a3~26@ d3~32@) (Mul d3~32@ a3~26@)) (Mul (Mul c3~30@
                         d3~32@
                        ) (Mul b3~28@ b3~28@)
                       )
                      ) b3~28@
                    ))
                    (=>
                     (= temp_3_1~777@ (Mul (Mul (Mul (Mul c3~30@ d3~32@) (Mul b3~28@ b3~28@)) (Mul (Mul a3~26@
                          d3~32@
                         ) (Mul d3~32@ a3~26@)
                        )
                       ) b3~28@
                     ))
                     (=>
                      (= tmp%4@ (= temp_3_0~740@ temp_3_1~777@))
                      (and
                       (=>
                        %%location_label%%3
                        tmp%4@
                       )
                       (=>
                        tmp%4@
                        (=>
                         (= temp_4_0~829@ (Sub (Mul (Mul (Mul c4~38@ d4~40@) (Sub c4~38@ d4~40@)) a4~34@) (Mul
                            (Mul b4~36@ (Mul a4~34@ a4~34@)) d4~40@
                         )))
                         (=>
                          (= temp_4_1~874@ (Sub (Mul (Sub (Mul (Mul c4~38@ d4~40@) c4~38@) (Mul (Mul c4~38@ d4~40@)
                               d4~40@
                              )
                             ) a4~34@
                            ) (Mul (Mul b4~36@ (Mul a4~34@ a4~34@)) d4~40@)
                          ))
                          (=>
                           (= tmp%5@ (= temp_4_0~829@ temp_4_1~874@))
                           (and
                            (=>
                             %%location_label%%4
                             tmp%5@
                            )
                            (=>
                             tmp%5@
                             (=>
                              (= temp_5_0~938@ (Mul (Sub (Sub (Mul c5~46@ d5~48@) (Mul b5~44@ a5~42@)) (Mul (Mul b5~44@
                                   40
                                  ) (Sub d5~48@ b5~44@)
                                 )
                                ) c5~46@
                              ))
                              (=>
                               (= temp_5_1~1007@ (Mul (Sub (Sub (Mul c5~46@ d5~48@) (Mul b5~44@ a5~42@)) (Sub (Mul (Mul
                                     b5~44@ 40
                                    ) d5~48@
                                   ) (Mul (Mul b5~44@ 40) b5~44@)
                                  )
                                 ) c5~46@
                               ))
                               (=>
                                (= tmp%6@ (= temp_5_0~938@ temp_5_1~1007@))
                                (and
                                 (=>
                                  %%location_label%%5
                                  tmp%6@
                                 )
                                 (=>
                                  tmp%6@
                                  (=>
                                   (= temp_6_0~1099@ (Add (Mul (Mul (Mul d6~56@ b6~52@) (Mul d6~56@ b6~52@)) (Add (Mul 73
                                        a6~50@
                                       ) (Mul d6~56@ b6~52@)
                                      )
                                     ) (Mul (Mul (Mul b6~52@ b6~52@) (Mul c6~54@ a6~50@)) (Mul (Mul a6~50@ a6~50@) (Mul b6~52@
                                        d6~56@
                                   )))))
                                   (=>
                                    (= temp_6_1~1176@ (Add (Mul (Mul (Mul d6~56@ b6~52@) (Mul d6~56@ b6~52@)) (Add (Mul 73
                                         a6~50@
                                        ) (Mul d6~56@ b6~52@)
                                       )
                                      ) (Mul (Mul (Mul b6~52@ b6~52@) (Mul a6~50@ c6~54@)) (Mul (Mul a6~50@ a6~50@) (Mul b6~52@
                                         d6~56@
                                    )))))
                                    (=>
                                     (= tmp%7@ (= temp_6_0~1099@ temp_6_1~1176@))
                                     (and
                                      (=>
                                       %%location_label%%6
                                       tmp%7@
                                      )
                                      (=>
                                       tmp%7@
                                       (=>
                                        (= temp_7_0~1264@ (Mul (Mul (Mul (Mul a7~58@ b7~60@) (Mul d7~64@ c7~62@)) (Mul (Mul a7~58@
                                             d7~64@
                                            ) a7~58@
                                           )
                                          ) (Add (Mul (Mul 49 a7~58@) (Mul c7~62@ d7~64@)) (Add (Sub d7~64@ d7~64@) (Mul d7~64@
                                             b7~60@
                                        )))))
                                        (=>
                                         (= temp_7_1~1365@ (Add (Mul (Mul (Mul (Mul a7~58@ b7~60@) (Mul d7~64@ c7~62@)) (Mul (Mul
                                               a7~58@ d7~64@
                                              ) a7~58@
                                             )
                                            ) (Mul (Mul 49 a7~58@) (Mul c7~62@ d7~64@))
                                           ) (Mul (Mul (Mul (Mul a7~58@ b7~60@) (Mul d7~64@ c7~62@)) (Mul (Mul a7~58@ d7~64@) a7~58@))
                                            (Add (Sub d7~64@ d7~64@) (Mul d7~64@ b7~60@))
                                         )))
                                         (=>
                                          (= tmp%8@ (= temp_7_0~1264@ temp_7_1~1365@))
                                          (and
                                           (=>
                                            %%location_label%%7
                                            tmp%8@
                                           )
                                           (=>
                                            tmp%8@
                                            (=>
                                             (= temp_8_0~1453@ (Mul (Mul (Mul (Mul a8~66@ 20) (Mul d8~72@ b8~68@)) (Sub (Mul b8~68@
                                                  d8~72@
                                                 ) (Add a8~66@ c8~70@)
                                                )
                                               ) (Mul (Mul (Mul b8~68@ b8~68@) (Mul c8~70@ d8~72@)) (Mul (Mul a8~66@ c8~70@) b8~68@))
                                             ))
                                             (=>
                                              (= temp_8_1~1526@ (Mul (Mul (Mul (Mul a8~66@ 20) (Mul d8~72@ b8~68@)) (Sub (Mul b8~68@
                                                   d8~72@
                                                  ) (Add a8~66@ c8~70@)
                                                 )
                                                ) (Mul (Mul (Mul b8~68@ b8~68@) (Mul c8~70@ d8~72@)) (Mul b8~68@ (Mul a8~66@ c8~70@)))
                                              ))
                                              (=>
                                               (= tmp%9@ (= temp_8_0~1453@ temp_8_1~1526@))
                                               (and
                                                (=>
                                                 %%location_label%%8
                                                 tmp%9@
                                                )
                                                (=>
                                                 tmp%9@
                                                 (=>
                                                  (= temp_9_0~1606@ (Mul (Mul (Mul (Mul c9~78@ d9~80@) (Mul b9~76@ a9~74@)) (Mul (Mul a9~74@
                                                       a9~74@
                                                      ) (Mul c9~78@ d9~80@)
                                                     )
                                                    ) (Mul (Sub (Mul b9~76@ d9~80@) (Mul b9~76@ b9~76@)) (Mul (Mul d9~80@ d9~80@) (Mul b9~76@
                                                       b9~76@
                                                  )))))
                                                  (=>
                                                   (= temp_9_1~1671@ (Mul (Mul (Mul (Mul d9~80@ c9~78@) (Mul b9~76@ a9~74@)) (Mul (Mul a9~74@
                                                        a9~74@
                                                       ) (Mul c9~78@ d9~80@)
                                                      )
                                                     ) (Mul (Sub (Mul b9~76@ d9~80@) (Mul b9~76@ b9~76@)) (Mul (Mul d9~80@ d9~80@) (Mul b9~76@
                                                        b9~76@
                                                   )))))
                                                   (=>
                                                    (= tmp%10@ (= temp_9_0~1606@ temp_9_1~1671@))
                                                    (and
                                                     (=>
                                                      %%location_label%%9
                                                      tmp%10@
                                                     )
                                                     (=>
                                                      tmp%10@
                                                      (=>
                                                       (= temp_10_0~1747@ (Mul (Sub (Mul (Mul c10~86@ d10~88@) (Sub b10~84@ b10~84@)) (Mul (
                                                            Mul c10~86@ c10~86@
                                                           ) d10~88@
                                                          )
                                                         ) (Mul (Mul (Mul c10~86@ a10~82@) (Mul d10~88@ a10~82@)) (Mul (Add d10~88@ a10~82@)
                                                           (Mul c10~86@ d10~88@)
                                                       ))))
                                                       (=>
                                                        (= temp_10_1~1808@ (Mul (Sub (Mul (Mul c10~86@ d10~88@) (Sub b10~84@ b10~84@)) (Mul c10~86@
                                                            (Mul c10~86@ d10~88@)
                                                           )
                                                          ) (Mul (Mul (Mul c10~86@ a10~82@) (Mul d10~88@ a10~82@)) (Mul (Add d10~88@ a10~82@)
                                                            (Mul c10~86@ d10~88@)
                                                        ))))
                                                        (=>
                                                         (= tmp%11@ (= temp_10_0~1747@ temp_10_1~1808@))
                                                         (and
                                                          (=>
                                                           %%location_label%%10
                                                           tmp%11@
                                                          )
                                                          (=>
                                                           tmp%11@
                                                           (=>
                                                            (= temp_11_0~1872@ (Mul (Mul a11~90@ (Mul (Mul a11~90@ d11~96@) (Mul c11~94@ c11~94@)))
                                                              (Mul (Mul (Mul b11~92@ a11~90@) d11~96@) (Add (Mul d11~96@ b11~92@) (Mul a11~90@ c11~94@)))
                                                            ))
                                                            (=>
                                                             (= temp_11_1~1921@ (Mul (Mul a11~90@ (Mul (Mul a11~90@ d11~96@) (Mul c11~94@ c11~94@)))
                                                               (Mul (Mul b11~92@ (Mul a11~90@ d11~96@)) (Add (Mul d11~96@ b11~92@) (Mul a11~90@ c11~94@)))
                                                             ))
                                                             (=>
                                                              (= tmp%12@ (= temp_11_0~1872@ temp_11_1~1921@))
                                                              (and
                                                               (=>
                                                                %%location_label%%11
                                                                tmp%12@
                                                               )
                                                               (=>
                                                                tmp%12@
                                                                (=>
                                                                 (= temp_12_0~1989@ (Mul (Mul d12~104@ (Mul (Mul d12~104@ a12~98@) (Mul b12~100@ a12~98@)))
                                                                   (Mul (Mul (Add d12~104@ a12~98@) (Mul d12~104@ d12~104@)) (Sub (Mul a12~98@ a12~98@)
                                                                     (Mul c12~102@ d12~104@)
                                                                 ))))
                                                                 (=>
                                                                  (= temp_12_1~2042@ (Mul (Mul d12~104@ (Mul (Mul d12~104@ a12~98@) (Mul b12~100@ a12~98@)))
                                                                    (Mul (Mul (Mul d12~104@ d12~104@) (Add d12~104@ a12~98@)) (Sub (Mul a12~98@ a12~98@)
                                                                      (Mul c12~102@ d12~104@)
                                                                  ))))
                                                                  (=>
                                                                   (= tmp%13@ (= temp_12_0~1989@ temp_12_1~2042@))
                                                                   (and
                                                                    (=>
                                                                     %%location_label%%12
                                                                     tmp%13@
                                                                    )
                                                                    (=>
                                                                     tmp%13@
                                                                     (=>
                                                                      (= temp_13_0~2094@ (Mul a13~106@ (Mul (Sub (Mul c13~110@ c13~110@) (Mul b13~108@ b13~108@))
                                                                         (Mul (Mul c13~110@ b13~108@) (Mul c13~110@ a13~106@))
                                                                      )))
                                                                      (=>
                                                                       (= temp_13_1~2147@ (Mul a13~106@ (Sub (Mul (Mul c13~110@ c13~110@) (Mul (Mul c13~110@ b13~108@)
                                                                            (Mul c13~110@ a13~106@)
                                                                           )
                                                                          ) (Mul (Mul b13~108@ b13~108@) (Mul (Mul c13~110@ b13~108@) (Mul c13~110@ a13~106@)))
                                                                       )))
                                                                       (=>
                                                                        (= tmp%14@ (= temp_13_0~2094@ temp_13_1~2147@))
                                                                        (and
                                                                         (=>
                                                                          %%location_label%%13
                                                                          tmp%14@
                                                                         )
                                                                         (=>
                                                                          tmp%14@
                                                                          (=>
                                                                           (= temp_14_0~2235@ (Mul (Mul (Mul (Mul d14~120@ b14~116@) (Mul a14~114@ b14~116@)) (
                                                                               Mul (Mul d14~120@ a14~114@) (Mul c14~118@ d14~120@)
                                                                              )
                                                                             ) (Mul (Mul (Mul b14~116@ b14~116@) (Mul b14~116@ b14~116@)) (Mul (Mul a14~114@ 8)
                                                                               b14~116@
                                                                           ))))
                                                                           (=>
                                                                            (= temp_14_1~2308@ (Mul (Mul (Mul (Mul d14~120@ b14~116@) (Mul a14~114@ b14~116@)) (
                                                                                Mul (Mul d14~120@ a14~114@) (Mul d14~120@ c14~118@)
                                                                               )
                                                                              ) (Mul (Mul (Mul b14~116@ b14~116@) (Mul b14~116@ b14~116@)) (Mul (Mul a14~114@ 8)
                                                                                b14~116@
                                                                            ))))
                                                                            (=>
                                                                             (= tmp%15@ (= temp_14_0~2235@ temp_14_1~2308@))
                                                                             (and
                                                                              (=>
                                                                               %%location_label%%14
                                                                               tmp%15@
                                                                              )
                                                                              (=>
                                                                               tmp%15@
                                                                               (=>
                                                                                (= temp_15_0~2388@ (Mul (Add (Mul (Add b15~124@ c15~126@) (Mul c15~126@ c15~126@)) (
                                                                                    Mul (Mul b15~124@ d15~128@) (Mul c15~126@ a15~122@)
                                                                                   )
                                                                                  ) (Mul (Mul (Mul a15~122@ d15~128@) (Mul a15~122@ b15~124@)) (Mul (Sub b15~124@ d15~128@)
                                                                                    (Add c15~126@ d15~128@)
                                                                                ))))
                                                                                (=>
                                                                                 (= temp_15_1~2453@ (Mul (Add (Mul (Add b15~124@ c15~126@) (Mul c15~126@ c15~126@)) (
                                                                                     Mul (Mul b15~124@ d15~128@) (Mul c15~126@ a15~122@)
                                                                                    )
                                                                                   ) (Mul (Mul (Mul a15~122@ d15~128@) (Mul a15~122@ b15~124@)) (Mul (Sub b15~124@ d15~128@)
                                                                                     (Add c15~126@ d15~128@)
                                                                                 ))))
                                                                                 (=>
                                                                                  (= tmp%16@ (= temp_15_0~2388@ temp_15_1~2453@))
                                                                                  (and
                                                                                   (=>
                                                                                    %%location_label%%15
                                                                                    tmp%16@
                                                                                   )
                                                                                   (=>
                                                                                    tmp%16@
                                                                                    (=>
                                                                                     (= temp_16_0~2541@ (Mul (Add (Mul (Sub c16~134@ b16~132@) (Mul c16~134@ b16~132@)) (
                                                                                         Mul (Add c16~134@ a16~130@) (Sub a16~130@ 70)
                                                                                        )
                                                                                       ) (Mul (Mul b16~132@ (Mul c16~134@ a16~130@)) (Sub (Mul d16~136@ a16~130@) (Mul c16~134@
                                                                                          a16~130@
                                                                                     )))))
                                                                                     (=>
                                                                                      (= temp_16_1~2614@ (Mul (Add (Mul (Sub c16~134@ b16~132@) (Mul c16~134@ b16~132@)) (
                                                                                          Mul (Sub a16~130@ 70) (Add c16~134@ a16~130@)
                                                                                         )
                                                                                        ) (Mul (Mul b16~132@ (Mul c16~134@ a16~130@)) (Sub (Mul d16~136@ a16~130@) (Mul c16~134@
                                                                                           a16~130@
                                                                                      )))))
                                                                                      (=>
                                                                                       (= tmp%17@ (= temp_16_0~2541@ temp_16_1~2614@))
                                                                                       (and
                                                                                        (=>
                                                                                         %%location_label%%16
                                                                                         tmp%17@
                                                                                        )
                                                                                        (=>
                                                                                         tmp%17@
                                                                                         (=>
                                                                                          (= temp_17_0~2706@ (Sub (Mul (Sub (Mul 16 d17~144@) (Mul d17~144@ b17~140@)) (Sub (Add
                                                                                               a17~138@ c17~142@
                                                                                              ) (Mul 21 d17~144@)
                                                                                             )
                                                                                            ) (Mul (Mul (Sub a17~138@ b17~140@) (Mul d17~144@ d17~144@)) c17~142@)
                                                                                          ))
                                                                                          (=>
                                                                                           (= temp_17_1~2783@ (Sub (Mul (Sub (Mul 16 d17~144@) (Mul d17~144@ b17~140@)) (Sub (Add
                                                                                                a17~138@ c17~142@
                                                                                               ) (Mul 21 d17~144@)
                                                                                              )
                                                                                             ) (Mul (Mul (Mul d17~144@ d17~144@) (Sub a17~138@ b17~140@)) c17~142@)
                                                                                           ))
                                                                                           (=>
                                                                                            (= tmp%18@ (= temp_17_0~2706@ temp_17_1~2783@))
                                                                                            (and
                                                                                             (=>
                                                                                              %%location_label%%17
                                                                                              tmp%18@
                                                                                             )
                                                                                             (=>
                                                                                              tmp%18@
                                                                                              (=>
                                                                                               (= temp_18_0~2863@ (Mul (Sub (Mul (Sub b18~148@ a18~146@) (Mul d18~152@ b18~148@)) (
                                                                                                   Mul (Mul a18~146@ c18~150@) (Sub d18~152@ c18~150@)
                                                                                                  )
                                                                                                 ) (Mul (Add (Sub b18~148@ b18~148@) (Mul b18~148@ d18~152@)) (Mul (Mul c18~150@ d18~152@)
                                                                                                   (Mul a18~146@ a18~146@)
                                                                                               ))))
                                                                                               (=>
                                                                                                (= temp_18_1~2928@ (Mul (Mul (Sub (Mul (Sub b18~148@ a18~146@) (Mul d18~152@ b18~148@))
                                                                                                    (Mul (Mul a18~146@ c18~150@) (Sub d18~152@ c18~150@))
                                                                                                   ) (Add (Sub b18~148@ b18~148@) (Mul b18~148@ d18~152@))
                                                                                                  ) (Mul (Mul c18~150@ d18~152@) (Mul a18~146@ a18~146@))
                                                                                                ))
                                                                                                (=>
                                                                                                 (= tmp%19@ (= temp_18_0~2863@ temp_18_1~2928@))
                                                                                                 (and
                                                                                                  (=>
                                                                                                   %%location_label%%18
                                                                                                   tmp%19@
                                                                                                  )
                                                                                                  (=>
                                                                                                   tmp%19@
                                                                                                   (=>
                                                                                                    (= temp_19_0~2996@ (Mul (Mul a19~154@ (Mul (Add d19~160@ b19~156@) (Mul c19~158@ c19~158@)))
                                                                                                      (Mul (Sub (Mul c19~158@ d19~160@) (Sub d19~160@ a19~154@)) (Add (Mul d19~160@ b19~156@)
                                                                                                        (Mul c19~158@ a19~154@)
                                                                                                    ))))
                                                                                                    (=>
                                                                                                     (= temp_19_1~3049@ (Mul (Mul a19~154@ (Mul (Add d19~160@ b19~156@) (Mul c19~158@ c19~158@)))
                                                                                                       (Mul (Add (Mul d19~160@ b19~156@) (Mul c19~158@ a19~154@)) (Sub (Mul c19~158@ d19~160@)
                                                                                                         (Sub d19~160@ a19~154@)
                                                                                                     ))))
                                                                                                     (=>
                                                                                                      (= tmp%20@ (= temp_19_0~2996@ temp_19_1~3049@))
                                                                                                      (=>
                                                                                                       %%location_label%%19
                                                                                                       tmp%20@
 ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
 (get-info :version)
 (assert
  %%query%%
 )
 (set-option :rlimit 4294967295)
 (check-sat)
 (set-option :rlimit 0)
(pop)
