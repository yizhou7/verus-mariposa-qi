use builtin_macros::*;
use builtin::*;

verus! {

// #[verifier::external_body]
// pub proof fn lemma_small_div_converse_auto()
//     ensures forall |x: int, d:int| 0 <= x && 0 < d && #[trigger] (x / d) == 0 ==> x < d
// {}

// proof fn bar(a: int, b: int, c: int, N: int) by(integer_ring)
//     requires (a - b) % N == 0
//     ensures (a * c - b * c) % N == 0
// {}

// proof fn foo(a: int, b: int, c: int, N: int)
// requires N != 0,
//     (a - b) % N == 0
// {
//     bar(a, b, c, N);
//     assert ((a * c - b * c) % N == 0);
// }

#[verifier::external_body]
pub proof fn lemma_mul_is_associative_auto()
    ensures
        forall |x: int, y: int, z: int| 
            #[trigger](x * (y * z)) == #[trigger]((x * y) * z)
{}

#[verifier::external_body]
pub proof fn lemma_mul_is_associative(x: int, y: int, z: int)
    ensures
        (x * (y * z)) == ((x * y) * z)
{}

#[verifier::external_body]
pub proof fn lemma_mul_is_commutative_auto()
    ensures
        forall |x: int, y: int|
            #[trigger](x * y) == (y * x)
{}

#[verifier::external_body]
pub proof fn lemma_mul_is_commutative(x: int, y: int)
    ensures (x * y) == (y * x)
{}

#[verifier::external_body]
pub proof fn lemma_mul_is_distributive_auto()
    ensures
        forall |x: int, y: int, z: int|
            #[trigger](x * (y + z)) == ((x * y) + (x * z)),
        forall |x: int, y: int, z: int|
            #[trigger]((x + y) * z) == ((x * z) + (y * z)),
        forall |x: int, y: int, z: int|
            #[trigger](x * (y - z)) == ((x * y) - (x * z)),
        forall |x: int, y: int, z: int|
            #[trigger]((x - y) * z) == ((x * z) - (y * z))
{}

#[verifier::external_body]
pub proof fn lemma_mul_is_distributive_inverse_auto()
    ensures
        forall |x: int, y: int, z: int|
            (x * (y + z)) == #[trigger]((x * y) + (x * z)),
        forall |x: int, y: int, z: int|
            ((x + y) * z) == #[trigger]((x * z) + (y * z)),
        forall |x: int, y: int, z: int|
            (x * (y - z)) == #[trigger]((x * y) - (x * z)),
        forall |x: int, y: int, z: int|
            ((x - y) * z) == #[trigger]((x * z) - (y * z))
{}

#[verifier::external_body]
pub proof fn lemma_mul_is_distributive(x: int, y: int, z: int)
    ensures
        (x * (y + z)) == ((x * y) + (x * z)),
        ((x + y) * z) == ((x * z) + (y * z)),
        (x * (y - z)) == ((x * y) - (x * z)),
        ((x - y) * z) == ((x * z) - (y * z))
{}

#[verifier::external_body]
pub proof fn lemma_mod_mul_noop(x: int, y: int, m: int)
    requires
        m > 0
    ensures
        (x * y) % m == ((x % m) * (y % m)) % m,
        (x * y) % m == (x * (y % m)) % m,
        (x * y) % m == ((x % m) * y) % m
{}

#[verifier::external_body]
pub proof fn lemma_mod_mul_cong(x: int, y: int, z: int, m: int)
    requires
        m > 0,
        x % m == y % m
    ensures
        (x * z) % m == (y * z) % m
{}

#[verifier::external_body]
pub proof fn lemma_mul_properties_auto_0()
    ensures
        forall |x: int, y: int|
            #![trigger x * y] #![trigger y * x]
            x * y == y * x,
        forall |x: int, y: int, z: int|
            #![trigger x * (y * z)] #![trigger (x * y) * z]
            x * (y * z) == (x * y) * z,
        forall |x: int, y: int, z: int|
            #![trigger x * (y + z)] #![trigger (x * y) + (x * z)]
           x * (y + z) == (x * y) + (x * z),
        forall |x: int, y: int, z: int|
            #![trigger (x + y) * z] #![trigger (x * z) + (y * z)]
            (x + y) * z == (x * z) + (y * z),
        forall |x: int, y: int, z: int|
            #![trigger x * (y - z)] #![trigger (x * y) - (x * z)]
            x * (y - z) == (x * y) - (x * z),
        forall |x: int, y: int, z: int|
            #![trigger (x - y) * z] #![trigger (x * z) - (y * z)]
            (x - y) * z == (x * z) - (y * z),
{}

// I think this is the same as the above, maybe slightly worse

#[verifier::external_body]
pub proof fn lemma_mul_properties_auto_1()
    ensures
        forall |x: int, y: int|
            #[trigger](x * y) == (y * x),
        forall |x: int, y: int, z: int|
            #[trigger](x * (y * z)) == ((x * y) * z),
        forall |x: int, y: int, z: int|
            (x * (y * z)) == #[trigger]((x * y) * z),
        forall |x: int, y: int, z: int|
            #[trigger](x * (y + z)) == ((x * y) + (x * z)),
        forall |x: int, y: int, z: int|
            #[trigger]((x + y) * z) == ((x * z) + (y * z)),
        forall |x: int, y: int, z: int|
            #[trigger](x * (y - z)) == ((x * y) - (x * z)),
        forall |x: int, y: int, z: int|
            #[trigger]((x - y) * z) == ((x * z) - (y * z)),
        forall |x: int, y: int, z: int|
            (x * (y + z)) == #[trigger]((x * y) + (x * z)),
        forall |x: int, y: int, z: int|
            ((x + y) * z) == #[trigger]((x * z) + (y * z)),
        forall |x: int, y: int, z: int|
            (x * (y - z)) == #[trigger]((x * y) - (x * z)),
        forall |x: int, y: int, z: int|
            ((x - y) * z) == #[trigger]((x * z) - (y * z)),
{}

// I think using multi-pattern is incomplete
// it might be fine in single step mode (?)

#[verifier::external_body]
pub proof fn lemma_mul_properties_auto_2()
    ensures
        forall |x: int, y: int|
            #[trigger](x * y) == #[trigger](y * x),
        forall |x: int, y: int, z: int|
            #[trigger](x * (y * z)) == #[trigger](x * y) * z,
        forall |x: int, y: int, z: int|
            #[trigger](x * (y + z)) == #[trigger]((x * y) + (x * z)),
        forall |x: int, y: int, z: int|
            #[trigger]((x + y) * z) == #[trigger]((x * z) + (y * z)),
        forall |x: int, y: int, z: int|
            #[trigger](x * (y - z)) == #[trigger]((x * y) - (x * z)),
        forall |x: int, y: int, z: int|
            #[trigger]((x - y) * z) == #[trigger]((x * z) - (y * z)),
{}

} // verus!

