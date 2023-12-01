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
pub proof fn lemma_mul_properties_auto()
    ensures
        forall |x: int, y: int, z: int|
            #[trigger](x * (y + z)) == ((x * y) + (x * z)),
        forall |x: int, y: int, z: int|
            #[trigger]((x + y) * z) == ((x * z) + (y * z)),
        forall |x: int, y: int, z: int|
            #[trigger](x * (y - z)) == ((x * y) - (x * z)),
        forall |x: int, y: int, z: int|
            #[trigger]((x - y) * z) == ((x * z) - (y * z)),
        forall |x: int, y: int|
            #[trigger](x * y) == (y * x),
        forall |x: int, y: int, z: int|
            #[trigger](x * (y * z)) == #[trigger]((x * y) * z),
        forall |x: int, y: int, z: int|
            (x * (y + z)) == #[trigger]((x * y) + (x * z)),
        forall |x: int, y: int, z: int|
            ((x + y) * z) == #[trigger]((x * z) + (y * z)),
        forall |x: int, y: int, z: int|
            (x * (y - z)) == #[trigger]((x * y) - (x * z)),
        forall |x: int, y: int, z: int|
            ((x - y) * z) == #[trigger]((x * z) - (y * z))
{}

// #[verifier::external_body]
// pub proof fn lemma_mul_add_is_distributive(x: int, y: int, z: int)
//     ensures
//         (x * (y + z)) == ((x * y) + (x * z)),
//         ((x + y) * z) == ((x * z) + (y * z))
// {}

// #[verifier::external_body]
// pub proof fn lemma_mul_add_is_left_distributive_auto()
//     ensures forall |x: int, y: int, z: int|
//         #[trigger](x * (y + z)) == ((x * y) + (x * z))
// {}

// #[verifier::external_body]
// pub proof fn lemma_mul_add_is_left_distributive(x: int, y: int, z: int)
//     ensures
//         (x * (y + z)) == ((x * y) + (x * z))
// {}

// #[verifier::external_body]
// pub proof fn lemma_mul_add_is_right_distributive_auto()
//     ensures forall |x: int, y: int, z: int|
//         #[trigger]((x + y) * z) == ((x * z) + (y * z))
// {}

// #[verifier::external_body]
// pub proof fn lemma_mul_add_is_right_distributive(x: int, y: int, z: int)
//     ensures
//         ((x + y) * z) == ((x * z) + (y * z)),
// {}

// #[verifier::external_body]
// pub proof fn lemma_mul_sub_is_left_distributive_auto()
//     ensures forall |x: int, y: int, z: int|
//         #[trigger](x * (y - z)) == ((x * y) - (x * z))
// {}

// #[verifier::external_body]
// pub proof fn lemma_mul_sub_is_left_distributive(x: int, y: int, z: int)
//     ensures
//         (x * (y - z)) == ((x * y) - (x * z))
// {}

// #[verifier::external_body]
// pub proof fn lemma_mul_sub_is_right_distributive_auto()
//     ensures forall |x: int, y: int, z: int|
//         #[trigger]((x - y) * z) == ((x * z) - (y * z))
// {}

// #[verifier::external_body]
// pub proof fn lemma_mul_sub_is_right_distributive(x: int, y: int, z: int)
//     ensures
//         ((x - y) * z) == ((x * z) - (y * z))
// {}
} // verus!

