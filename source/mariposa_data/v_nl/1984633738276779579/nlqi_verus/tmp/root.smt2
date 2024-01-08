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
;; mariposa_data/v_nl//1984633738276779579/nlqi_verus/src/main.rs:7:1: 36:40 (#0)
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
 (declare-const tmp%25@ Bool)
 (declare-const tmp%26@ Bool)
 (declare-const temp_0_0~297@ Int)
 (declare-const temp_0_1~354@ Int)
 (declare-const temp_1_0~422@ Int)
 (declare-const temp_1_1~491@ Int)
 (declare-const temp_2_0~567@ Int)
 (declare-const temp_2_1~628@ Int)
 (declare-const temp_3_0~716@ Int)
 (declare-const temp_3_1~789@ Int)
 (declare-const temp_4_0~877@ Int)
 (declare-const temp_4_1~950@ Int)
 (declare-const temp_5_0~1030@ Int)
 (declare-const temp_5_1~1095@ Int)
 (declare-const temp_6_0~1199@ Int)
 (declare-const temp_6_1~1304@ Int)
 (declare-const temp_7_0~1380@ Int)
 (declare-const temp_7_1~1441@ Int)
 (declare-const temp_8_0~1513@ Int)
 (declare-const temp_8_1~1570@ Int)
 (declare-const temp_9_0~1634@ Int)
 (declare-const temp_9_1~1683@ Int)
 (declare-const temp_10_0~1763@ Int)
 (declare-const temp_10_1~1836@ Int)
 (declare-const temp_11_0~1916@ Int)
 (declare-const temp_11_1~1981@ Int)
 (declare-const temp_12_0~2057@ Int)
 (declare-const temp_12_1~2118@ Int)
 (declare-const temp_13_0~2206@ Int)
 (declare-const temp_13_1~2291@ Int)
 (declare-const temp_14_0~2371@ Int)
 (declare-const temp_14_1~2444@ Int)
 (declare-const temp_15_0~2520@ Int)
 (declare-const temp_15_1~2581@ Int)
 (declare-const temp_16_0~2657@ Int)
 (declare-const temp_16_1~2718@ Int)
 (declare-const temp_17_0~2794@ Int)
 (declare-const temp_17_1~2855@ Int)
 (declare-const temp_18_0~2935@ Int)
 (declare-const temp_18_1~3000@ Int)
 (declare-const temp_19_0~3072@ Int)
 (declare-const temp_19_1~3137@ Int)
 (declare-const temp_20_0~3217@ Int)
 (declare-const temp_20_1~3282@ Int)
 (declare-const temp_21_0~3362@ Int)
 (declare-const temp_21_1~3427@ Int)
 (declare-const temp_22_0~3507@ Int)
 (declare-const temp_22_1~3572@ Int)
 (declare-const temp_23_0~3628@ Int)
 (declare-const temp_23_1~3669@ Int)
 (declare-const temp_24_0~3749@ Int)
 (declare-const temp_24_1~3814@ Int)
 (declare-const temp_25_0~3906@ Int)
 (declare-const temp_25_1~3983@ Int)
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
 (declare-const %%query%% Bool)
 (assert
  (=>
   %%query%%
   (not (=>
     (= temp_0_0~297@ (Mul (Add (Mul d0~8@ (Mul b0~4@ c0~6@)) (Mul (Mul a0~2@ d0~8@) (Mul c0~6@
          d0~8@
        ))
       ) (Mul (Add (Mul c0~6@ b0~4@) (Mul d0~8@ c0~6@)) (Mul (Add b0~4@ b0~4@) d0~8@))
     ))
     (=>
      (= temp_0_1~354@ (Mul (Add (Mul d0~8@ (Mul b0~4@ c0~6@)) (Mul (Mul a0~2@ d0~8@) (Mul c0~6@
           d0~8@
         ))
        ) (Mul (Mul (Add b0~4@ b0~4@) d0~8@) (Add (Mul c0~6@ b0~4@) (Mul d0~8@ c0~6@)))
      ))
      (=>
       (= tmp%1@ (= temp_0_0~297@ temp_0_1~354@))
       (and
        (=>
         %%location_label%%0
         tmp%1@
        )
        (=>
         tmp%1@
         (=>
          (= temp_1_0~422@ (Mul (Mul (Sub (Mul a1~10@ a1~10@) (Add d1~16@ a1~10@)) (Mul (Mul d1~16@
               d1~16@
              ) (Mul a1~10@ b1~12@)
             )
            ) (Add (Mul (Mul a1~10@ b1~12@) (Mul b1~12@ d1~16@)) b1~12@)
          ))
          (=>
           (= temp_1_1~491@ (Mul (Sub (Mul (Mul a1~10@ a1~10@) (Mul (Mul d1~16@ d1~16@) (Mul a1~10@
                 b1~12@
               ))
              ) (Mul (Add d1~16@ a1~10@) (Mul (Mul d1~16@ d1~16@) (Mul a1~10@ b1~12@)))
             ) (Add (Mul (Mul a1~10@ b1~12@) (Mul b1~12@ d1~16@)) b1~12@)
           ))
           (=>
            (= tmp%2@ (= temp_1_0~422@ temp_1_1~491@))
            (and
             (=>
              %%location_label%%1
              tmp%2@
             )
             (=>
              tmp%2@
              (=>
               (= temp_2_0~567@ (Mul (Mul (Mul (Mul a2~18@ c2~22@) (Mul c2~22@ a2~18@)) (Mul (Add b2~20@
                    a2~18@
                   ) (Add d2~24@ b2~20@)
                  )
                 ) (Mul (Mul (Mul a2~18@ d2~24@) c2~22@) (Add (Mul a2~18@ c2~22@) (Mul c2~22@ d2~24@)))
               ))
               (=>
                (= temp_2_1~628@ (Mul (Mul (Mul (Mul a2~18@ c2~22@) (Mul c2~22@ a2~18@)) (Mul (Add b2~20@
                     a2~18@
                    ) (Add d2~24@ b2~20@)
                   )
                  ) (Mul (Mul c2~22@ (Mul a2~18@ d2~24@)) (Add (Mul a2~18@ c2~22@) (Mul c2~22@ d2~24@)))
                ))
                (=>
                 (= tmp%3@ (= temp_2_0~567@ temp_2_1~628@))
                 (and
                  (=>
                   %%location_label%%2
                   tmp%3@
                  )
                  (=>
                   tmp%3@
                   (=>
                    (= temp_3_0~716@ (Mul (Mul (Mul (Mul a3~26@ b3~28@) a3~26@) (Mul (Add a3~26@ c3~30@)
                        (Mul d3~32@ d3~32@)
                       )
                      ) (Add (Mul (Mul a3~26@ d3~32@) (Mul a3~26@ c3~30@)) (Sub (Sub c3~30@ d3~32@) (Mul 92
                         d3~32@
                    )))))
                    (=>
                     (= temp_3_1~789@ (Mul (Mul (Mul (Mul a3~26@ b3~28@) a3~26@) (Mul (Add a3~26@ c3~30@)
                         (Mul d3~32@ d3~32@)
                        )
                       ) (Add (Mul (Mul d3~32@ a3~26@) (Mul a3~26@ c3~30@)) (Sub (Sub c3~30@ d3~32@) (Mul 92
                          d3~32@
                     )))))
                     (=>
                      (= tmp%4@ (= temp_3_0~716@ temp_3_1~789@))
                      (and
                       (=>
                        %%location_label%%3
                        tmp%4@
                       )
                       (=>
                        tmp%4@
                        (=>
                         (= temp_4_0~877@ (Add (Add (Sub (Add d4~40@ a4~34@) (Mul a4~34@ d4~40@)) (Mul a4~34@
                             (Sub c4~38@ c4~38@)
                            )
                           ) (Mul (Mul (Mul 3 d4~40@) (Mul c4~38@ a4~34@)) (Mul (Mul a4~34@ b4~36@) (Mul c4~38@
                              b4~36@
                         )))))
                         (=>
                          (= temp_4_1~950@ (Add (Add (Sub (Add d4~40@ a4~34@) (Mul a4~34@ d4~40@)) (Mul a4~34@
                              (Sub c4~38@ c4~38@)
                             )
                            ) (Mul (Mul (Mul c4~38@ a4~34@) (Mul 3 d4~40@)) (Mul (Mul a4~34@ b4~36@) (Mul c4~38@
                               b4~36@
                          )))))
                          (=>
                           (= tmp%5@ (= temp_4_0~877@ temp_4_1~950@))
                           (and
                            (=>
                             %%location_label%%4
                             tmp%5@
                            )
                            (=>
                             tmp%5@
                             (=>
                              (= temp_5_0~1030@ (Mul (Mul (Mul (Mul c5~46@ d5~48@) (Mul c5~46@ a5~42@)) (Sub (Mul d5~48@
                                   d5~48@
                                  ) (Mul b5~44@ a5~42@)
                                 )
                                ) (Mul (Mul (Mul a5~42@ c5~46@) (Mul d5~48@ a5~42@)) (Mul (Mul c5~46@ d5~48@) (Mul c5~46@
                                   b5~44@
                              )))))
                              (=>
                               (= temp_5_1~1095@ (Mul (Mul (Mul (Mul c5~46@ d5~48@) (Mul c5~46@ a5~42@)) (Sub (Mul d5~48@
                                    d5~48@
                                   ) (Mul b5~44@ a5~42@)
                                  )
                                 ) (Mul (Mul (Mul (Mul a5~42@ c5~46@) (Mul d5~48@ a5~42@)) (Mul c5~46@ d5~48@)) (Mul
                                   c5~46@ b5~44@
                               ))))
                               (=>
                                (= tmp%6@ (= temp_5_0~1030@ temp_5_1~1095@))
                                (and
                                 (=>
                                  %%location_label%%5
                                  tmp%6@
                                 )
                                 (=>
                                  tmp%6@
                                  (=>
                                   (= temp_6_0~1199@ (Mul (Mul (Sub (Sub b6~52@ b6~52@) (Mul d6~56@ b6~52@)) (Mul (Mul d6~56@
                                        d6~56@
                                       ) (Mul d6~56@ c6~54@)
                                      )
                                     ) (Sub (Mul (Mul c6~54@ 87) (Sub c6~54@ b6~52@)) (Sub (Add 91 c6~54@) (Mul c6~54@ d6~56@)))
                                   ))
                                   (=>
                                    (= temp_6_1~1304@ (Mul (Sub (Mul (Sub b6~52@ b6~52@) (Mul (Mul d6~56@ d6~56@) (Mul d6~56@
                                          c6~54@
                                        ))
                                       ) (Mul (Mul d6~56@ b6~52@) (Mul (Mul d6~56@ d6~56@) (Mul d6~56@ c6~54@)))
                                      ) (Sub (Mul (Mul c6~54@ 87) (Sub c6~54@ b6~52@)) (Sub (Add 91 c6~54@) (Mul c6~54@ d6~56@)))
                                    ))
                                    (=>
                                     (= tmp%7@ (= temp_6_0~1199@ temp_6_1~1304@))
                                     (and
                                      (=>
                                       %%location_label%%6
                                       tmp%7@
                                      )
                                      (=>
                                       tmp%7@
                                       (=>
                                        (= temp_7_0~1380@ (Mul (Sub (Sub (Mul c7~62@ a7~58@) d7~64@) (Mul (Mul a7~58@ a7~58@)
                                            (Sub a7~58@ d7~64@)
                                           )
                                          ) (Mul (Mul (Mul b7~60@ d7~64@) (Mul b7~60@ d7~64@)) (Add (Mul d7~64@ c7~62@) (Mul c7~62@
                                             a7~58@
                                        )))))
                                        (=>
                                         (= temp_7_1~1441@ (Mul (Sub (Sub (Mul c7~62@ a7~58@) d7~64@) (Mul (Sub a7~58@ d7~64@)
                                             (Mul a7~58@ a7~58@)
                                            )
                                           ) (Mul (Mul (Mul b7~60@ d7~64@) (Mul b7~60@ d7~64@)) (Add (Mul d7~64@ c7~62@) (Mul c7~62@
                                              a7~58@
                                         )))))
                                         (=>
                                          (= tmp%8@ (= temp_7_0~1380@ temp_7_1~1441@))
                                          (and
                                           (=>
                                            %%location_label%%7
                                            tmp%8@
                                           )
                                           (=>
                                            tmp%8@
                                            (=>
                                             (= temp_8_0~1513@ (Sub (Sub (Mul (Mul c8~70@ d8~72@) (Add d8~72@ b8~68@)) (Mul (Mul b8~68@
                                                  a8~66@
                                                 ) (Mul c8~70@ d8~72@)
                                                )
                                               ) (Sub (Mul (Mul a8~66@ d8~72@) (Sub d8~72@ d8~72@)) (Mul c8~70@ b8~68@))
                                             ))
                                             (=>
                                              (= temp_8_1~1570@ (Sub (Sub (Mul (Mul c8~70@ d8~72@) (Add d8~72@ b8~68@)) (Mul (Mul b8~68@
                                                   a8~66@
                                                  ) (Mul c8~70@ d8~72@)
                                                 )
                                                ) (Sub (Mul (Sub d8~72@ d8~72@) (Mul a8~66@ d8~72@)) (Mul c8~70@ b8~68@))
                                              ))
                                              (=>
                                               (= tmp%9@ (= temp_8_0~1513@ temp_8_1~1570@))
                                               (and
                                                (=>
                                                 %%location_label%%8
                                                 tmp%9@
                                                )
                                                (=>
                                                 tmp%9@
                                                 (=>
                                                  (= temp_9_0~1634@ (Mul a9~74@ (Mul (Mul (Mul b9~76@ 33) (Mul d9~80@ a9~74@)) (Mul (Mul
                                                       a9~74@ a9~74@
                                                      ) (Mul d9~80@ c9~78@)
                                                  ))))
                                                  (=>
                                                   (= temp_9_1~1683@ (Mul a9~74@ (Mul (Mul (Mul d9~80@ a9~74@) (Mul b9~76@ 33)) (Mul (Mul
                                                        a9~74@ a9~74@
                                                       ) (Mul d9~80@ c9~78@)
                                                   ))))
                                                   (=>
                                                    (= tmp%10@ (= temp_9_0~1634@ temp_9_1~1683@))
                                                    (and
                                                     (=>
                                                      %%location_label%%9
                                                      tmp%10@
                                                     )
                                                     (=>
                                                      tmp%10@
                                                      (=>
                                                       (= temp_10_0~1763@ (Sub (Mul (Mul (Sub b10~84@ b10~84@) (Mul a10~82@ c10~86@)) (Mul (
                                                            Mul a10~82@ d10~88@
                                                           ) (Mul b10~84@ a10~82@)
                                                          )
                                                         ) (Mul (Mul (Mul c10~86@ a10~82@) (Mul a10~82@ a10~82@)) (Mul (Mul b10~84@ b10~84@)
                                                           (Mul c10~86@ b10~84@)
                                                       ))))
                                                       (=>
                                                        (= temp_10_1~1836@ (Sub (Mul (Sub (Mul b10~84@ (Mul a10~82@ c10~86@)) (Mul b10~84@ (Mul
                                                              a10~82@ c10~86@
                                                            ))
                                                           ) (Mul (Mul a10~82@ d10~88@) (Mul b10~84@ a10~82@))
                                                          ) (Mul (Mul (Mul c10~86@ a10~82@) (Mul a10~82@ a10~82@)) (Mul (Mul b10~84@ b10~84@)
                                                            (Mul c10~86@ b10~84@)
                                                        ))))
                                                        (=>
                                                         (= tmp%11@ (= temp_10_0~1763@ temp_10_1~1836@))
                                                         (and
                                                          (=>
                                                           %%location_label%%10
                                                           tmp%11@
                                                          )
                                                          (=>
                                                           tmp%11@
                                                           (=>
                                                            (= temp_11_0~1916@ (Mul (Mul (Mul (Mul c11~94@ b11~92@) (Mul d11~96@ c11~94@)) (Sub (
                                                                 Mul d11~96@ a11~90@
                                                                ) (Mul d11~96@ d11~96@)
                                                               )
                                                              ) (Mul (Mul (Mul b11~92@ d11~96@) (Mul a11~90@ a11~90@)) (Add (Mul c11~94@ a11~90@)
                                                                (Add d11~96@ a11~90@)
                                                            ))))
                                                            (=>
                                                             (= temp_11_1~1981@ (Mul (Mul (Mul (Mul c11~94@ b11~92@) (Mul d11~96@ c11~94@)) (Sub (
                                                                  Mul d11~96@ a11~90@
                                                                 ) (Mul d11~96@ d11~96@)
                                                                )
                                                               ) (Mul (Mul b11~92@ d11~96@) (Mul (Mul a11~90@ a11~90@) (Add (Mul c11~94@ a11~90@) (
                                                                   Add d11~96@ a11~90@
                                                             ))))))
                                                             (=>
                                                              (= tmp%12@ (= temp_11_0~1916@ temp_11_1~1981@))
                                                              (and
                                                               (=>
                                                                %%location_label%%11
                                                                tmp%12@
                                                               )
                                                               (=>
                                                                tmp%12@
                                                                (=>
                                                                 (= temp_12_0~2057@ (Mul (Mul (Mul a12~98@ (Mul b12~100@ c12~102@)) (Add (Mul c12~102@
                                                                      c12~102@
                                                                     ) (Mul a12~98@ d12~104@)
                                                                    )
                                                                   ) (Mul (Mul (Mul c12~102@ d12~104@) (Add b12~100@ d12~104@)) (Mul (Mul d12~104@ a12~98@)
                                                                     (Mul a12~98@ d12~104@)
                                                                 ))))
                                                                 (=>
                                                                  (= temp_12_1~2118@ (Mul (Mul (Mul a12~98@ (Mul b12~100@ c12~102@)) (Add (Mul c12~102@
                                                                       c12~102@
                                                                      ) (Mul d12~104@ a12~98@)
                                                                     )
                                                                    ) (Mul (Mul (Mul c12~102@ d12~104@) (Add b12~100@ d12~104@)) (Mul (Mul d12~104@ a12~98@)
                                                                      (Mul a12~98@ d12~104@)
                                                                  ))))
                                                                  (=>
                                                                   (= tmp%13@ (= temp_12_0~2057@ temp_12_1~2118@))
                                                                   (and
                                                                    (=>
                                                                     %%location_label%%12
                                                                     tmp%13@
                                                                    )
                                                                    (=>
                                                                     tmp%13@
                                                                     (=>
                                                                      (= temp_13_0~2206@ (Mul (Mul (Sub (Add c13~110@ 99) (Mul c13~110@ a13~106@)) (Add (Mul
                                                                           d13~112@ c13~110@
                                                                          ) a13~106@
                                                                         )
                                                                        ) (Sub (Mul (Mul a13~106@ b13~108@) (Mul d13~112@ a13~106@)) (Mul (Mul c13~110@ b13~108@)
                                                                          (Mul c13~110@ d13~112@)
                                                                      ))))
                                                                      (=>
                                                                       (= temp_13_1~2291@ (Mul (Sub (Mul (Add c13~110@ 99) (Add (Mul d13~112@ c13~110@) a13~106@))
                                                                          (Mul (Mul c13~110@ a13~106@) (Add (Mul d13~112@ c13~110@) a13~106@))
                                                                         ) (Sub (Mul (Mul a13~106@ b13~108@) (Mul d13~112@ a13~106@)) (Mul (Mul c13~110@ b13~108@)
                                                                           (Mul c13~110@ d13~112@)
                                                                       ))))
                                                                       (=>
                                                                        (= tmp%14@ (= temp_13_0~2206@ temp_13_1~2291@))
                                                                        (and
                                                                         (=>
                                                                          %%location_label%%13
                                                                          tmp%14@
                                                                         )
                                                                         (=>
                                                                          tmp%14@
                                                                          (=>
                                                                           (= temp_14_0~2371@ (Mul (Mul (Sub (Mul d14~120@ a14~114@) (Mul b14~116@ d14~120@)) a14~114@)
                                                                             (Mul (Mul (Add a14~114@ b14~116@) (Mul a14~114@ c14~118@)) (Mul (Mul d14~120@ 47) (
                                                                                Sub c14~118@ b14~116@
                                                                           )))))
                                                                           (=>
                                                                            (= temp_14_1~2444@ (Mul (Mul (Sub (Mul d14~120@ a14~114@) (Mul b14~116@ d14~120@)) a14~114@)
                                                                              (Mul (Add (Mul a14~114@ (Mul a14~114@ c14~118@)) (Mul b14~116@ (Mul a14~114@ c14~118@)))
                                                                               (Mul (Mul d14~120@ 47) (Sub c14~118@ b14~116@))
                                                                            )))
                                                                            (=>
                                                                             (= tmp%15@ (= temp_14_0~2371@ temp_14_1~2444@))
                                                                             (and
                                                                              (=>
                                                                               %%location_label%%14
                                                                               tmp%15@
                                                                              )
                                                                              (=>
                                                                               tmp%15@
                                                                               (=>
                                                                                (= temp_15_0~2520@ (Sub (Mul (Mul (Mul c15~126@ b15~124@) a15~122@) (Mul (Mul b15~124@
                                                                                     b15~124@
                                                                                    ) (Mul a15~122@ b15~124@)
                                                                                   )
                                                                                  ) (Mul (Mul (Mul d15~128@ a15~122@) (Sub c15~126@ b15~124@)) (Mul (Mul b15~124@ b15~124@)
                                                                                    (Mul b15~124@ b15~124@)
                                                                                ))))
                                                                                (=>
                                                                                 (= temp_15_1~2581@ (Sub (Mul (Mul (Mul c15~126@ b15~124@) a15~122@) (Mul (Mul b15~124@
                                                                                      b15~124@
                                                                                     ) (Mul b15~124@ a15~122@)
                                                                                    )
                                                                                   ) (Mul (Mul (Mul d15~128@ a15~122@) (Sub c15~126@ b15~124@)) (Mul (Mul b15~124@ b15~124@)
                                                                                     (Mul b15~124@ b15~124@)
                                                                                 ))))
                                                                                 (=>
                                                                                  (= tmp%16@ (= temp_15_0~2520@ temp_15_1~2581@))
                                                                                  (and
                                                                                   (=>
                                                                                    %%location_label%%15
                                                                                    tmp%16@
                                                                                   )
                                                                                   (=>
                                                                                    tmp%16@
                                                                                    (=>
                                                                                     (= temp_16_0~2657@ (Mul (Mul (Add a16~130@ (Mul c16~134@ a16~130@)) (Mul (Mul d16~136@
                                                                                          d16~136@
                                                                                         ) (Mul d16~136@ d16~136@)
                                                                                        )
                                                                                       ) (Mul (Mul (Mul c16~134@ b16~132@) (Mul d16~136@ b16~132@)) (Mul (Add a16~130@ c16~134@)
                                                                                         (Mul b16~132@ c16~134@)
                                                                                     ))))
                                                                                     (=>
                                                                                      (= temp_16_1~2718@ (Mul (Mul (Add a16~130@ (Mul c16~134@ a16~130@)) (Mul (Mul d16~136@
                                                                                           d16~136@
                                                                                          ) (Mul d16~136@ d16~136@)
                                                                                         )
                                                                                        ) (Mul (Mul (Mul b16~132@ c16~134@) (Mul d16~136@ b16~132@)) (Mul (Add a16~130@ c16~134@)
                                                                                          (Mul b16~132@ c16~134@)
                                                                                      ))))
                                                                                      (=>
                                                                                       (= tmp%17@ (= temp_16_0~2657@ temp_16_1~2718@))
                                                                                       (and
                                                                                        (=>
                                                                                         %%location_label%%16
                                                                                         tmp%17@
                                                                                        )
                                                                                        (=>
                                                                                         tmp%17@
                                                                                         (=>
                                                                                          (= temp_17_0~2794@ (Mul (Mul (Mul (Mul d17~144@ b17~140@) d17~144@) (Mul (Mul a17~138@
                                                                                               c17~142@
                                                                                              ) (Mul b17~140@ d17~144@)
                                                                                             )
                                                                                            ) (Mul (Mul (Mul a17~138@ b17~140@) (Mul d17~144@ a17~138@)) (Mul (Mul a17~138@ c17~142@)
                                                                                              (Sub c17~142@ c17~142@)
                                                                                          ))))
                                                                                          (=>
                                                                                           (= temp_17_1~2855@ (Mul (Mul (Mul (Mul a17~138@ b17~140@) (Mul d17~144@ a17~138@)) (
                                                                                               Mul (Mul a17~138@ c17~142@) (Sub c17~142@ c17~142@)
                                                                                              )
                                                                                             ) (Mul (Mul (Mul d17~144@ b17~140@) d17~144@) (Mul (Mul a17~138@ c17~142@) (Mul b17~140@
                                                                                                d17~144@
                                                                                           )))))
                                                                                           (=>
                                                                                            (= tmp%18@ (= temp_17_0~2794@ temp_17_1~2855@))
                                                                                            (and
                                                                                             (=>
                                                                                              %%location_label%%17
                                                                                              tmp%18@
                                                                                             )
                                                                                             (=>
                                                                                              tmp%18@
                                                                                              (=>
                                                                                               (= temp_18_0~2935@ (Mul (Mul (Mul (Mul c18~150@ a18~146@) (Add a18~146@ c18~150@)) c18~150@)
                                                                                                 (Mul (Mul (Add c18~150@ c18~150@) (Mul c18~150@ b18~148@)) (Mul (Mul b18~148@ a18~146@)
                                                                                                   (Mul c18~150@ 68)
                                                                                               ))))
                                                                                               (=>
                                                                                                (= temp_18_1~3000@ (Mul (Mul (Mul c18~150@ a18~146@) (Mul (Add a18~146@ c18~150@) c18~150@))
                                                                                                  (Mul (Mul (Add c18~150@ c18~150@) (Mul c18~150@ b18~148@)) (Mul (Mul b18~148@ a18~146@)
                                                                                                    (Mul c18~150@ 68)
                                                                                                ))))
                                                                                                (=>
                                                                                                 (= tmp%19@ (= temp_18_0~2935@ temp_18_1~3000@))
                                                                                                 (and
                                                                                                  (=>
                                                                                                   %%location_label%%18
                                                                                                   tmp%19@
                                                                                                  )
                                                                                                  (=>
                                                                                                   tmp%19@
                                                                                                   (=>
                                                                                                    (= temp_19_0~3072@ (Sub (Mul (Mul (Mul b19~156@ c19~158@) c19~158@) (Mul b19~156@ (Mul
                                                                                                         b19~156@ c19~158@
                                                                                                       ))
                                                                                                      ) (Add (Mul (Add d19~160@ b19~156@) (Add c19~158@ b19~156@)) (Mul (Mul b19~156@ b19~156@)
                                                                                                        (Sub d19~160@ d19~160@)
                                                                                                    ))))
                                                                                                    (=>
                                                                                                     (= temp_19_1~3137@ (Sub (Mul (Mul (Mul b19~156@ c19~158@) c19~158@) (Mul b19~156@ (Mul
                                                                                                          b19~156@ c19~158@
                                                                                                        ))
                                                                                                       ) (Add (Mul (Add d19~160@ b19~156@) (Add c19~158@ b19~156@)) (Sub (Mul (Mul b19~156@
                                                                                                           b19~156@
                                                                                                          ) d19~160@
                                                                                                         ) (Mul (Mul b19~156@ b19~156@) d19~160@)
                                                                                                     ))))
                                                                                                     (=>
                                                                                                      (= tmp%20@ (= temp_19_0~3072@ temp_19_1~3137@))
                                                                                                      (and
                                                                                                       (=>
                                                                                                        %%location_label%%19
                                                                                                        tmp%20@
                                                                                                       )
                                                                                                       (=>
                                                                                                        tmp%20@
                                                                                                        (=>
                                                                                                         (= temp_20_0~3217@ (Add (Mul (Mul (Add d20~168@ d20~168@) (Mul a20~162@ b20~164@)) (
                                                                                                             Mul (Sub c20~166@ d20~168@) (Mul b20~164@ d20~168@)
                                                                                                            )
                                                                                                           ) (Mul (Add (Sub a20~162@ b20~164@) (Mul c20~166@ c20~166@)) (Mul (Mul c20~166@ c20~166@)
                                                                                                             (Mul a20~162@ b20~164@)
                                                                                                         ))))
                                                                                                         (=>
                                                                                                          (= temp_20_1~3282@ (Add (Mul (Mul (Add d20~168@ d20~168@) (Mul a20~162@ b20~164@)) (
                                                                                                              Mul (Sub c20~166@ d20~168@) (Mul b20~164@ d20~168@)
                                                                                                             )
                                                                                                            ) (Mul (Mul (Mul c20~166@ c20~166@) (Mul a20~162@ b20~164@)) (Add (Sub a20~162@ b20~164@)
                                                                                                              (Mul c20~166@ c20~166@)
                                                                                                          ))))
                                                                                                          (=>
                                                                                                           (= tmp%21@ (= temp_20_0~3217@ temp_20_1~3282@))
                                                                                                           (and
                                                                                                            (=>
                                                                                                             %%location_label%%20
                                                                                                             tmp%21@
                                                                                                            )
                                                                                                            (=>
                                                                                                             tmp%21@
                                                                                                             (=>
                                                                                                              (= temp_21_0~3362@ (Sub (Mul (Mul (Mul c21~174@ c21~174@) (Mul c21~174@ 45)) (Mul (Mul
                                                                                                                   d21~176@ a21~170@
                                                                                                                  ) (Mul b21~172@ b21~172@)
                                                                                                                 )
                                                                                                                ) (Mul (Mul (Mul b21~172@ b21~172@) (Add c21~174@ d21~176@)) d21~176@)
                                                                                                              ))
                                                                                                              (=>
                                                                                                               (= temp_21_1~3427@ (Sub (Mul (Mul (Mul c21~174@ 45) (Mul c21~174@ c21~174@)) (Mul (Mul
                                                                                                                    d21~176@ a21~170@
                                                                                                                   ) (Mul b21~172@ b21~172@)
                                                                                                                  )
                                                                                                                 ) (Mul (Mul (Mul b21~172@ b21~172@) (Add c21~174@ d21~176@)) d21~176@)
                                                                                                               ))
                                                                                                               (=>
                                                                                                                (= tmp%22@ (= temp_21_0~3362@ temp_21_1~3427@))
                                                                                                                (and
                                                                                                                 (=>
                                                                                                                  %%location_label%%21
                                                                                                                  tmp%22@
                                                                                                                 )
                                                                                                                 (=>
                                                                                                                  tmp%22@
                                                                                                                  (=>
                                                                                                                   (= temp_22_0~3507@ (Sub (Mul (Mul (Add d22~184@ c22~182@) (Mul d22~184@ c22~182@)) (
                                                                                                                       Mul (Mul b22~180@ a22~178@) (Mul a22~178@ c22~182@)
                                                                                                                      )
                                                                                                                     ) (Mul (Mul (Add d22~184@ b22~180@) (Mul b22~180@ d22~184@)) (Mul (Mul b22~180@ a22~178@)
                                                                                                                       (Mul c22~182@ a22~178@)
                                                                                                                   ))))
                                                                                                                   (=>
                                                                                                                    (= temp_22_1~3572@ (Sub (Mul (Mul (Mul (Add d22~184@ c22~182@) (Mul d22~184@ c22~182@))
                                                                                                                        (Mul b22~180@ a22~178@)
                                                                                                                       ) (Mul a22~178@ c22~182@)
                                                                                                                      ) (Mul (Mul (Add d22~184@ b22~180@) (Mul b22~180@ d22~184@)) (Mul (Mul b22~180@ a22~178@)
                                                                                                                        (Mul c22~182@ a22~178@)
                                                                                                                    ))))
                                                                                                                    (=>
                                                                                                                     (= tmp%23@ (= temp_22_0~3507@ temp_22_1~3572@))
                                                                                                                     (and
                                                                                                                      (=>
                                                                                                                       %%location_label%%22
                                                                                                                       tmp%23@
                                                                                                                      )
                                                                                                                      (=>
                                                                                                                       tmp%23@
                                                                                                                       (=>
                                                                                                                        (= temp_23_0~3628@ (Mul (Mul d23~192@ (Mul (Mul c23~190@ c23~190@) (Mul a23~186@ d23~192@)))
                                                                                                                          (Mul d23~192@ (Mul (Mul d23~192@ c23~190@) (Mul b23~188@ c23~190@)))
                                                                                                                        ))
                                                                                                                        (=>
                                                                                                                         (= temp_23_1~3669@ (Mul (Mul d23~192@ (Mul (Mul c23~190@ c23~190@) (Mul a23~186@ d23~192@)))
                                                                                                                           (Mul (Mul (Mul d23~192@ c23~190@) (Mul b23~188@ c23~190@)) d23~192@)
                                                                                                                         ))
                                                                                                                         (=>
                                                                                                                          (= tmp%24@ (= temp_23_0~3628@ temp_23_1~3669@))
                                                                                                                          (and
                                                                                                                           (=>
                                                                                                                            %%location_label%%23
                                                                                                                            tmp%24@
                                                                                                                           )
                                                                                                                           (=>
                                                                                                                            tmp%24@
                                                                                                                            (=>
                                                                                                                             (= temp_24_0~3749@ (Mul (Sub (Mul (Mul b24~196@ d24~200@) (Mul d24~200@ b24~196@)) (
                                                                                                                                 Mul (Mul d24~200@ d24~200@) (Mul d24~200@ b24~196@)
                                                                                                                                )
                                                                                                                               ) (Mul (Mul (Mul a24~194@ d24~200@) (Sub d24~200@ a24~194@)) (Mul (Sub c24~198@ d24~200@)
                                                                                                                                 (Add b24~196@ d24~200@)
                                                                                                                             ))))
                                                                                                                             (=>
                                                                                                                              (= temp_24_1~3814@ (Mul (Sub (Mul (Mul b24~196@ d24~200@) (Mul d24~200@ b24~196@)) (
                                                                                                                                  Mul (Mul d24~200@ b24~196@) (Mul d24~200@ d24~200@)
                                                                                                                                 )
                                                                                                                                ) (Mul (Mul (Mul a24~194@ d24~200@) (Sub d24~200@ a24~194@)) (Mul (Sub c24~198@ d24~200@)
                                                                                                                                  (Add b24~196@ d24~200@)
                                                                                                                              ))))
                                                                                                                              (=>
                                                                                                                               (= tmp%25@ (= temp_24_0~3749@ temp_24_1~3814@))
                                                                                                                               (and
                                                                                                                                (=>
                                                                                                                                 %%location_label%%24
                                                                                                                                 tmp%25@
                                                                                                                                )
                                                                                                                                (=>
                                                                                                                                 tmp%25@
                                                                                                                                 (=>
                                                                                                                                  (= temp_25_0~3906@ (Mul (Sub (Mul (Mul d25~208@ d25~208@) (Mul a25~202@ c25~206@)) (
                                                                                                                                      Mul (Mul d25~208@ d25~208@) (Mul b25~204@ b25~204@)
                                                                                                                                     )
                                                                                                                                    ) (Mul (Mul (Sub a25~202@ d25~208@) (Mul d25~208@ a25~202@)) (Mul (Sub 3 c25~206@)
                                                                                                                                      (Add d25~208@ a25~202@)
                                                                                                                                  ))))
                                                                                                                                  (=>
                                                                                                                                   (= temp_25_1~3983@ (Mul (Sub (Mul (Mul d25~208@ d25~208@) (Mul a25~202@ c25~206@)) (
                                                                                                                                       Mul (Mul b25~204@ b25~204@) (Mul d25~208@ d25~208@)
                                                                                                                                      )
                                                                                                                                     ) (Mul (Mul (Sub a25~202@ d25~208@) (Mul d25~208@ a25~202@)) (Mul (Sub 3 c25~206@)
                                                                                                                                       (Add d25~208@ a25~202@)
                                                                                                                                   ))))
                                                                                                                                   (=>
                                                                                                                                    (= tmp%26@ (= temp_25_0~3906@ temp_25_1~3983@))
                                                                                                                                    (=>
                                                                                                                                     %%location_label%%25
                                                                                                                                     tmp%26@
 ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
 (get-info :version)
 (assert
  %%query%%
 )
 (set-option :rlimit 4294967295)
 (check-sat)
 (set-option :rlimit 0)
(pop)
