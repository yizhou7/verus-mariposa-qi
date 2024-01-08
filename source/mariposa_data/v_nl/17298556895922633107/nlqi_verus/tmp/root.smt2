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
;; mariposa_data/v_nl//17298556895922633107/nlqi_verus/src/main.rs:7:1: 36:40 (#0)
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
 (declare-const temp_0_0~293@ Int)
 (declare-const temp_0_1~346@ Int)
 (declare-const temp_1_0~410@ Int)
 (declare-const temp_1_1~459@ Int)
 (declare-const temp_2_0~535@ Int)
 (declare-const temp_2_1~612@ Int)
 (declare-const temp_3_0~704@ Int)
 (declare-const temp_3_1~781@ Int)
 (declare-const temp_4_0~869@ Int)
 (declare-const temp_4_1~942@ Int)
 (declare-const temp_5_0~1022@ Int)
 (declare-const temp_5_1~1103@ Int)
 (declare-const temp_6_0~1191@ Int)
 (declare-const temp_6_1~1264@ Int)
 (declare-const temp_7_0~1320@ Int)
 (declare-const temp_7_1~1361@ Int)
 (declare-const temp_8_0~1441@ Int)
 (declare-const temp_8_1~1514@ Int)
 (declare-const temp_9_0~1590@ Int)
 (declare-const temp_9_1~1659@ Int)
 (declare-const temp_10_0~1739@ Int)
 (declare-const temp_10_1~1804@ Int)
 (declare-const temp_11_0~1884@ Int)
 (declare-const temp_11_1~1949@ Int)
 (declare-const temp_12_0~2025@ Int)
 (declare-const temp_12_1~2086@ Int)
 (declare-const temp_13_0~2162@ Int)
 (declare-const temp_13_1~2223@ Int)
 (declare-const temp_14_0~2315@ Int)
 (declare-const temp_14_1~2424@ Int)
 (declare-const temp_15_0~2512@ Int)
 (declare-const temp_15_1~2585@ Int)
 (declare-const temp_16_0~2665@ Int)
 (declare-const temp_16_1~2730@ Int)
 (declare-const temp_17_0~2822@ Int)
 (declare-const temp_17_1~2899@ Int)
 (declare-const temp_18_0~2975@ Int)
 (declare-const temp_18_1~3036@ Int)
 (declare-const temp_19_0~3128@ Int)
 (declare-const temp_19_1~3205@ Int)
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
     (= temp_0_0~293@ (Mul (Mul (Sub (Mul c0~6@ b0~4@) (Mul b0~4@ c0~6@)) (Mul (Mul a0~2@ b0~4@)
         (Add d0~8@ a0~2@)
        )
       ) (Mul a0~2@ (Sub (Mul a0~2@ d0~8@) (Mul b0~4@ a0~2@)))
     ))
     (=>
      (= temp_0_1~346@ (Mul (Mul (Sub (Mul b0~4@ c0~6@) (Mul b0~4@ c0~6@)) (Mul (Mul a0~2@ b0~4@)
          (Add d0~8@ a0~2@)
         )
        ) (Mul a0~2@ (Sub (Mul a0~2@ d0~8@) (Mul b0~4@ a0~2@)))
      ))
      (=>
       (= tmp%1@ (= temp_0_0~293@ temp_0_1~346@))
       (and
        (=>
         %%location_label%%0
         tmp%1@
        )
        (=>
         tmp%1@
         (=>
          (= temp_1_0~410@ (Mul (Mul (Sub (Mul d1~16@ c1~14@) b1~12@) a1~10@) (Mul (Mul (Mul b1~12@
               c1~14@
              ) (Mul b1~12@ a1~10@)
             ) (Mul (Mul b1~12@ c1~14@) (Mul d1~16@ a1~10@))
          )))
          (=>
           (= temp_1_1~459@ (Mul (Mul (Sub (Mul d1~16@ c1~14@) b1~12@) a1~10@) (Mul (Mul (Mul b1~12@
                c1~14@
               ) (Mul b1~12@ a1~10@)
              ) (Mul (Mul (Mul b1~12@ c1~14@) d1~16@) a1~10@)
           )))
           (=>
            (= tmp%2@ (= temp_1_0~410@ temp_1_1~459@))
            (and
             (=>
              %%location_label%%1
              tmp%2@
             )
             (=>
              tmp%2@
              (=>
               (= temp_2_0~535@ (Mul (Mul (Sub (Mul b2~20@ b2~20@) (Mul d2~24@ c2~22@)) (Sub c2~22@
                   (Mul c2~22@ b2~20@)
                  )
                 ) (Mul (Add (Mul a2~18@ c2~22@) (Mul a2~18@ c2~22@)) (Mul (Mul b2~20@ a2~18@) (Add b2~20@
                    d2~24@
               )))))
               (=>
                (= temp_2_1~612@ (Mul (Sub (Mul (Sub (Mul b2~20@ b2~20@) (Mul d2~24@ c2~22@)) c2~22@)
                   (Mul (Sub (Mul b2~20@ b2~20@) (Mul d2~24@ c2~22@)) (Mul c2~22@ b2~20@))
                  ) (Mul (Add (Mul a2~18@ c2~22@) (Mul a2~18@ c2~22@)) (Mul (Mul b2~20@ a2~18@) (Add b2~20@
                     d2~24@
                )))))
                (=>
                 (= tmp%3@ (= temp_2_0~535@ temp_2_1~612@))
                 (and
                  (=>
                   %%location_label%%2
                   tmp%3@
                  )
                  (=>
                   tmp%3@
                   (=>
                    (= temp_3_0~704@ (Add (Mul (Mul (Sub b3~28@ b3~28@) (Mul c3~30@ d3~32@)) (Mul (Mul 38
                         b3~28@
                        ) (Sub d3~32@ b3~28@)
                       )
                      ) (Mul (Mul (Mul a3~26@ a3~26@) (Sub c3~30@ d3~32@)) (Mul (Mul c3~30@ d3~32@) (Mul d3~32@
                         c3~30@
                    )))))
                    (=>
                     (= temp_3_1~781@ (Add (Mul (Mul (Sub b3~28@ b3~28@) (Mul c3~30@ d3~32@)) (Mul (Mul 38
                          b3~28@
                         ) (Sub d3~32@ b3~28@)
                        )
                       ) (Mul (Mul (Mul a3~26@ a3~26@) (Sub c3~30@ d3~32@)) (Mul (Mul d3~32@ c3~30@) (Mul d3~32@
                          c3~30@
                     )))))
                     (=>
                      (= tmp%4@ (= temp_3_0~704@ temp_3_1~781@))
                      (and
                       (=>
                        %%location_label%%3
                        tmp%4@
                       )
                       (=>
                        tmp%4@
                        (=>
                         (= temp_4_0~869@ (Mul (Mul (Mul (Mul a4~34@ d4~40@) (Mul c4~38@ d4~40@)) (Mul (Mul b4~36@
                              b4~36@
                             ) (Mul d4~40@ c4~38@)
                            )
                           ) (Sub (Mul (Add a4~34@ c4~38@) (Mul b4~36@ c4~38@)) (Mul a4~34@ (Mul 20 a4~34@)))
                         ))
                         (=>
                          (= temp_4_1~942@ (Mul (Mul (Mul (Mul d4~40@ a4~34@) (Mul c4~38@ d4~40@)) (Mul (Mul b4~36@
                               b4~36@
                              ) (Mul d4~40@ c4~38@)
                             )
                            ) (Sub (Mul (Add a4~34@ c4~38@) (Mul b4~36@ c4~38@)) (Mul a4~34@ (Mul 20 a4~34@)))
                          ))
                          (=>
                           (= tmp%5@ (= temp_4_0~869@ temp_4_1~942@))
                           (and
                            (=>
                             %%location_label%%4
                             tmp%5@
                            )
                            (=>
                             tmp%5@
                             (=>
                              (= temp_5_0~1022@ (Sub (Mul (Mul (Mul a5~42@ b5~44@) (Mul a5~42@ c5~46@)) (Mul (Mul a5~42@
                                   a5~42@
                                  ) (Mul a5~42@ b5~44@)
                                 )
                                ) (Mul (Mul (Mul c5~46@ d5~48@) (Mul a5~42@ c5~46@)) (Add (Sub c5~46@ b5~44@) (Add a5~42@
                                   c5~46@
                              )))))
                              (=>
                               (= temp_5_1~1103@ (Sub (Mul (Mul (Mul a5~42@ b5~44@) (Mul a5~42@ c5~46@)) (Mul (Mul a5~42@
                                    a5~42@
                                   ) (Mul a5~42@ b5~44@)
                                  )
                                 ) (Add (Mul (Mul (Mul c5~46@ d5~48@) (Mul a5~42@ c5~46@)) (Sub c5~46@ b5~44@)) (Mul
                                   (Mul (Mul c5~46@ d5~48@) (Mul a5~42@ c5~46@)) (Add a5~42@ c5~46@)
                               ))))
                               (=>
                                (= tmp%6@ (= temp_5_0~1022@ temp_5_1~1103@))
                                (and
                                 (=>
                                  %%location_label%%5
                                  tmp%6@
                                 )
                                 (=>
                                  tmp%6@
                                  (=>
                                   (= temp_6_0~1191@ (Mul (Mul (Mul (Mul b6~52@ b6~52@) b6~52@) (Mul (Mul c6~54@ c6~54@)
                                       (Mul d6~56@ c6~54@)
                                      )
                                     ) (Mul (Mul (Mul d6~56@ d6~56@) (Add d6~56@ 40)) (Mul (Mul b6~52@ b6~52@) (Mul c6~54@
                                        b6~52@
                                   )))))
                                   (=>
                                    (= temp_6_1~1264@ (Mul (Mul (Mul (Mul b6~52@ b6~52@) b6~52@) (Mul (Mul c6~54@ c6~54@)
                                        (Mul d6~56@ c6~54@)
                                       )
                                      ) (Mul (Mul (Mul d6~56@ d6~56@) (Add d6~56@ 40)) (Mul (Mul b6~52@ b6~52@) (Mul b6~52@
                                         c6~54@
                                    )))))
                                    (=>
                                     (= tmp%7@ (= temp_6_0~1191@ temp_6_1~1264@))
                                     (and
                                      (=>
                                       %%location_label%%6
                                       tmp%7@
                                      )
                                      (=>
                                       tmp%7@
                                       (=>
                                        (= temp_7_0~1320@ (Mul (Mul b7~60@ (Mul (Mul c7~62@ d7~64@) (Mul d7~64@ d7~64@))) (
                                           Mul (Mul (Mul c7~62@ c7~62@) (Add a7~58@ b7~60@)) b7~60@
                                        )))
                                        (=>
                                         (= temp_7_1~1361@ (Mul (Mul b7~60@ (Mul (Mul d7~64@ d7~64@) (Mul c7~62@ d7~64@))) (
                                            Mul (Mul (Mul c7~62@ c7~62@) (Add a7~58@ b7~60@)) b7~60@
                                         )))
                                         (=>
                                          (= tmp%8@ (= temp_7_0~1320@ temp_7_1~1361@))
                                          (and
                                           (=>
                                            %%location_label%%7
                                            tmp%8@
                                           )
                                           (=>
                                            tmp%8@
                                            (=>
                                             (= temp_8_0~1441@ (Mul (Mul (Mul (Add c8~70@ d8~72@) (Add d8~72@ c8~70@)) (Add (Add b8~68@
                                                  c8~70@
                                                 ) (Mul d8~72@ c8~70@)
                                                )
                                               ) (Mul (Sub (Mul b8~68@ a8~66@) (Mul b8~68@ d8~72@)) (Mul (Mul a8~66@ b8~68@) (Sub a8~66@
                                                  d8~72@
                                             )))))
                                             (=>
                                              (= temp_8_1~1514@ (Mul (Mul (Mul (Add c8~70@ d8~72@) (Add d8~72@ c8~70@)) (Add (Add b8~68@
                                                   c8~70@
                                                  ) (Mul d8~72@ c8~70@)
                                                 )
                                                ) (Mul (Sub (Mul b8~68@ a8~66@) (Mul b8~68@ d8~72@)) (Sub (Mul (Mul a8~66@ b8~68@) a8~66@)
                                                  (Mul (Mul a8~66@ b8~68@) d8~72@)
                                              ))))
                                              (=>
                                               (= tmp%9@ (= temp_8_0~1441@ temp_8_1~1514@))
                                               (and
                                                (=>
                                                 %%location_label%%8
                                                 tmp%9@
                                                )
                                                (=>
                                                 tmp%9@
                                                 (=>
                                                  (= temp_9_0~1590@ (Mul (Mul (Sub (Mul c9~78@ b9~76@) (Mul c9~78@ c9~78@)) (Mul (Sub c9~78@
                                                       a9~74@
                                                      ) (Mul a9~74@ d9~80@)
                                                     )
                                                    ) (Sub (Mul b9~76@ (Mul c9~78@ d9~80@)) (Mul (Mul b9~76@ d9~80@) (Mul a9~74@ b9~76@)))
                                                  ))
                                                  (=>
                                                   (= temp_9_1~1659@ (Mul (Mul (Sub (Mul c9~78@ b9~76@) (Mul c9~78@ c9~78@)) (Sub (Mul c9~78@
                                                        (Mul a9~74@ d9~80@)
                                                       ) (Mul a9~74@ (Mul a9~74@ d9~80@))
                                                      )
                                                     ) (Sub (Mul b9~76@ (Mul c9~78@ d9~80@)) (Mul (Mul b9~76@ d9~80@) (Mul a9~74@ b9~76@)))
                                                   ))
                                                   (=>
                                                    (= tmp%10@ (= temp_9_0~1590@ temp_9_1~1659@))
                                                    (and
                                                     (=>
                                                      %%location_label%%9
                                                      tmp%10@
                                                     )
                                                     (=>
                                                      tmp%10@
                                                      (=>
                                                       (= temp_10_0~1739@ (Mul (Mul (Mul (Mul a10~82@ b10~84@) (Mul a10~82@ c10~86@)) (Mul (
                                                            Sub a10~82@ b10~84@
                                                           ) (Mul b10~84@ c10~86@)
                                                          )
                                                         ) (Mul (Mul (Mul c10~86@ b10~84@) (Sub a10~82@ d10~88@)) (Add (Mul c10~86@ d10~88@)
                                                           (Mul d10~88@ a10~82@)
                                                       ))))
                                                       (=>
                                                        (= temp_10_1~1804@ (Mul (Mul (Mul (Mul c10~86@ b10~84@) (Sub a10~82@ d10~88@)) (Add (
                                                             Mul c10~86@ d10~88@
                                                            ) (Mul d10~88@ a10~82@)
                                                           )
                                                          ) (Mul (Mul (Mul a10~82@ b10~84@) (Mul a10~82@ c10~86@)) (Mul (Sub a10~82@ b10~84@)
                                                            (Mul b10~84@ c10~86@)
                                                        ))))
                                                        (=>
                                                         (= tmp%11@ (= temp_10_0~1739@ temp_10_1~1804@))
                                                         (and
                                                          (=>
                                                           %%location_label%%10
                                                           tmp%11@
                                                          )
                                                          (=>
                                                           tmp%11@
                                                           (=>
                                                            (= temp_11_0~1884@ (Add (Mul (Mul (Mul a11~90@ c11~94@) (Mul a11~90@ d11~96@)) (Mul (
                                                                 Add a11~90@ d11~96@
                                                                ) (Mul d11~96@ c11~94@)
                                                               )
                                                              ) (Mul (Mul (Mul c11~94@ c11~94@) (Mul a11~90@ a11~90@)) (Mul (Mul d11~96@ a11~90@)
                                                                (Mul b11~92@ c11~94@)
                                                            ))))
                                                            (=>
                                                             (= temp_11_1~1949@ (Add (Mul (Mul (Mul a11~90@ c11~94@) (Mul a11~90@ d11~96@)) (Mul (
                                                                  Add a11~90@ d11~96@
                                                                 ) (Mul d11~96@ c11~94@)
                                                                )
                                                               ) (Mul (Mul c11~94@ c11~94@) (Mul (Mul a11~90@ a11~90@) (Mul (Mul d11~96@ a11~90@) (
                                                                   Mul b11~92@ c11~94@
                                                             ))))))
                                                             (=>
                                                              (= tmp%12@ (= temp_11_0~1884@ temp_11_1~1949@))
                                                              (and
                                                               (=>
                                                                %%location_label%%11
                                                                tmp%12@
                                                               )
                                                               (=>
                                                                tmp%12@
                                                                (=>
                                                                 (= temp_12_0~2025@ (Add (Mul (Mul (Mul b12~100@ d12~104@) (Sub b12~100@ b12~100@)) (
                                                                     Mul b12~100@ (Mul d12~104@ c12~102@)
                                                                    )
                                                                   ) (Mul (Mul (Add a12~98@ c12~102@) (Add d12~104@ d12~104@)) (Mul (Mul b12~100@ a12~98@)
                                                                     (Mul a12~98@ d12~104@)
                                                                 ))))
                                                                 (=>
                                                                  (= temp_12_1~2086@ (Add (Mul (Mul (Mul b12~100@ d12~104@) (Sub b12~100@ b12~100@)) (
                                                                      Mul b12~100@ (Mul d12~104@ c12~102@)
                                                                     )
                                                                    ) (Mul (Mul (Mul b12~100@ a12~98@) (Mul a12~98@ d12~104@)) (Mul (Add a12~98@ c12~102@)
                                                                      (Add d12~104@ d12~104@)
                                                                  ))))
                                                                  (=>
                                                                   (= tmp%13@ (= temp_12_0~2025@ temp_12_1~2086@))
                                                                   (and
                                                                    (=>
                                                                     %%location_label%%12
                                                                     tmp%13@
                                                                    )
                                                                    (=>
                                                                     tmp%13@
                                                                     (=>
                                                                      (= temp_13_0~2162@ (Mul (Mul (Mul (Mul c13~110@ a13~106@) (Add d13~112@ d13~112@)) b13~108@)
                                                                        (Mul (Mul d13~112@ (Mul b13~108@ d13~112@)) (Add (Mul a13~106@ a13~106@) (Sub 86 b13~108@)))
                                                                      ))
                                                                      (=>
                                                                       (= temp_13_1~2223@ (Mul (Mul (Mul (Mul c13~110@ a13~106@) (Add d13~112@ d13~112@)) b13~108@)
                                                                         (Mul d13~112@ (Mul (Mul b13~108@ d13~112@) (Add (Mul a13~106@ a13~106@) (Sub 86 b13~108@))))
                                                                       ))
                                                                       (=>
                                                                        (= tmp%14@ (= temp_13_0~2162@ temp_13_1~2223@))
                                                                        (and
                                                                         (=>
                                                                          %%location_label%%13
                                                                          tmp%14@
                                                                         )
                                                                         (=>
                                                                          tmp%14@
                                                                          (=>
                                                                           (= temp_14_0~2315@ (Mul (Sub (Mul (Mul d14~120@ b14~116@) (Mul b14~116@ c14~118@)) (
                                                                               Add (Mul b14~116@ 92) (Sub d14~120@ c14~118@)
                                                                              )
                                                                             ) (Mul (Sub (Mul a14~114@ c14~118@) (Mul d14~120@ c14~118@)) (Mul (Mul a14~114@ c14~118@)
                                                                               (Mul b14~116@ b14~116@)
                                                                           ))))
                                                                           (=>
                                                                            (= temp_14_1~2424@ (Sub (Mul (Mul (Mul d14~120@ b14~116@) (Mul b14~116@ c14~118@)) (
                                                                                Mul (Sub (Mul a14~114@ c14~118@) (Mul d14~120@ c14~118@)) (Mul (Mul a14~114@ c14~118@)
                                                                                 (Mul b14~116@ b14~116@)
                                                                               ))
                                                                              ) (Mul (Add (Mul b14~116@ 92) (Sub d14~120@ c14~118@)) (Mul (Sub (Mul a14~114@ c14~118@)
                                                                                 (Mul d14~120@ c14~118@)
                                                                                ) (Mul (Mul a14~114@ c14~118@) (Mul b14~116@ b14~116@))
                                                                            ))))
                                                                            (=>
                                                                             (= tmp%15@ (= temp_14_0~2315@ temp_14_1~2424@))
                                                                             (and
                                                                              (=>
                                                                               %%location_label%%14
                                                                               tmp%15@
                                                                              )
                                                                              (=>
                                                                               tmp%15@
                                                                               (=>
                                                                                (= temp_15_0~2512@ (Mul (Mul (Mul (Mul b15~124@ a15~122@) b15~124@) (Mul (Add a15~122@
                                                                                     a15~122@
                                                                                    ) (Mul c15~126@ b15~124@)
                                                                                   )
                                                                                  ) (Mul (Mul (Mul 67 d15~128@) (Mul a15~122@ c15~126@)) (Mul (Mul a15~122@ a15~122@)
                                                                                    (Mul d15~128@ b15~124@)
                                                                                ))))
                                                                                (=>
                                                                                 (= temp_15_1~2585@ (Mul (Mul (Mul b15~124@ a15~122@) b15~124@) (Mul (Mul (Add a15~122@
                                                                                      a15~122@
                                                                                     ) (Mul c15~126@ b15~124@)
                                                                                    ) (Mul (Mul (Mul 67 d15~128@) (Mul a15~122@ c15~126@)) (Mul (Mul a15~122@ a15~122@)
                                                                                      (Mul d15~128@ b15~124@)
                                                                                 )))))
                                                                                 (=>
                                                                                  (= tmp%16@ (= temp_15_0~2512@ temp_15_1~2585@))
                                                                                  (and
                                                                                   (=>
                                                                                    %%location_label%%15
                                                                                    tmp%16@
                                                                                   )
                                                                                   (=>
                                                                                    tmp%16@
                                                                                    (=>
                                                                                     (= temp_16_0~2665@ (Mul (Mul (Mul (Mul 52 d16~136@) (Add b16~132@ a16~130@)) (Sub (Mul
                                                                                          c16~134@ c16~134@
                                                                                         ) (Mul a16~130@ d16~136@)
                                                                                        )
                                                                                       ) (Mul (Add (Mul d16~136@ c16~134@) (Mul c16~134@ b16~132@)) d16~136@)
                                                                                     ))
                                                                                     (=>
                                                                                      (= temp_16_1~2730@ (Mul (Mul (Mul (Mul 52 d16~136@) (Add b16~132@ a16~130@)) (Sub (Mul
                                                                                           c16~134@ c16~134@
                                                                                          ) (Mul a16~130@ d16~136@)
                                                                                         )
                                                                                        ) (Mul (Add (Mul c16~134@ d16~136@) (Mul c16~134@ b16~132@)) d16~136@)
                                                                                      ))
                                                                                      (=>
                                                                                       (= tmp%17@ (= temp_16_0~2665@ temp_16_1~2730@))
                                                                                       (and
                                                                                        (=>
                                                                                         %%location_label%%16
                                                                                         tmp%17@
                                                                                        )
                                                                                        (=>
                                                                                         tmp%17@
                                                                                         (=>
                                                                                          (= temp_17_0~2822@ (Mul (Mul (Mul (Mul a17~138@ c17~142@) (Sub b17~140@ d17~144@)) (
                                                                                              Mul (Mul c17~142@ d17~144@) (Mul 38 b17~140@)
                                                                                             )
                                                                                            ) (Mul (Sub (Mul b17~140@ b17~140@) (Mul c17~142@ a17~138@)) (Add (Mul c17~142@ b17~140@)
                                                                                              (Mul c17~142@ b17~140@)
                                                                                          ))))
                                                                                          (=>
                                                                                           (= temp_17_1~2899@ (Mul (Mul (Mul (Mul c17~142@ d17~144@) (Mul 38 b17~140@)) (Mul (Mul
                                                                                                a17~138@ c17~142@
                                                                                               ) (Sub b17~140@ d17~144@)
                                                                                              )
                                                                                             ) (Mul (Sub (Mul b17~140@ b17~140@) (Mul c17~142@ a17~138@)) (Add (Mul c17~142@ b17~140@)
                                                                                               (Mul c17~142@ b17~140@)
                                                                                           ))))
                                                                                           (=>
                                                                                            (= tmp%18@ (= temp_17_0~2822@ temp_17_1~2899@))
                                                                                            (and
                                                                                             (=>
                                                                                              %%location_label%%17
                                                                                              tmp%18@
                                                                                             )
                                                                                             (=>
                                                                                              tmp%18@
                                                                                              (=>
                                                                                               (= temp_18_0~2975@ (Mul (Add (Mul (Mul c18~150@ c18~150@) (Mul d18~152@ d18~152@)) (
                                                                                                   Mul (Mul c18~150@ b18~148@) (Mul d18~152@ d18~152@)
                                                                                                  )
                                                                                                 ) (Mul (Sub (Sub b18~148@ c18~150@) (Mul b18~148@ c18~150@)) (Mul (Mul b18~148@ b18~148@)
                                                                                                   c18~150@
                                                                                               ))))
                                                                                               (=>
                                                                                                (= temp_18_1~3036@ (Mul (Mul (Add (Mul (Mul c18~150@ c18~150@) (Mul d18~152@ d18~152@))
                                                                                                    (Mul (Mul c18~150@ b18~148@) (Mul d18~152@ d18~152@))
                                                                                                   ) (Sub (Sub b18~148@ c18~150@) (Mul b18~148@ c18~150@))
                                                                                                  ) (Mul (Mul b18~148@ b18~148@) c18~150@)
                                                                                                ))
                                                                                                (=>
                                                                                                 (= tmp%19@ (= temp_18_0~2975@ temp_18_1~3036@))
                                                                                                 (and
                                                                                                  (=>
                                                                                                   %%location_label%%18
                                                                                                   tmp%19@
                                                                                                  )
                                                                                                  (=>
                                                                                                   tmp%19@
                                                                                                   (=>
                                                                                                    (= temp_19_0~3128@ (Mul (Mul (Mul (Mul b19~156@ c19~158@) (Mul a19~154@ b19~156@)) (
                                                                                                        Mul (Add b19~156@ b19~156@) (Sub c19~158@ d19~160@)
                                                                                                       )
                                                                                                      ) (Add (Mul (Mul c19~158@ c19~158@) (Mul c19~158@ b19~156@)) (Mul (Mul b19~156@ b19~156@)
                                                                                                        (Mul 6 b19~156@)
                                                                                                    ))))
                                                                                                    (=>
                                                                                                     (= temp_19_1~3205@ (Mul (Mul (Mul (Mul b19~156@ c19~158@) (Mul b19~156@ a19~154@)) (
                                                                                                         Mul (Add b19~156@ b19~156@) (Sub c19~158@ d19~160@)
                                                                                                        )
                                                                                                       ) (Add (Mul (Mul c19~158@ c19~158@) (Mul c19~158@ b19~156@)) (Mul (Mul b19~156@ b19~156@)
                                                                                                         (Mul 6 b19~156@)
                                                                                                     ))))
                                                                                                     (=>
                                                                                                      (= tmp%20@ (= temp_19_0~3128@ temp_19_1~3205@))
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
