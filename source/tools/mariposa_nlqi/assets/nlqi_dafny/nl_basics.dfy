module nl_basics {

    lemma lemma_mul_is_associative(x: nat, y: nat, z: nat)
        ensures
            (x * (y * z)) == ((x * y) * z)

    lemma lemma_mul_is_commutative(x: nat, y: nat)
        ensures
            (x * y) == (y * x)

    lemma lemma_mul_is_distributive(x: nat, y: nat, z: nat)
        ensures
            (x * (y + z)) == ((x * y) + (x * z))
        ensures
            ((x + y) * z) == ((x * z) + (y * z))
        ensures
            (x * (y - z)) == ((x * y) - (x * z))
        ensures
            ((x - y) * z) == ((x * z) - (y * z))

    lemma lemma_mul_properties_auto_1()
    ensures
        forall x: nat, y: nat ::
            (x * y) == (y * x)
    ensures
        forall x: nat, y: nat, z: nat ::
            (x * (y * z)) == ((x * y) * z)
    ensures
        forall x: nat, y: nat, z: nat ::
            (x * (y * z)) == ((x * y) * z)
    ensures
        forall x: nat, y: nat, z: nat ::
            (x * (y + z)) == ((x * y) + (x * z))
    ensures
        forall x: nat, y: nat, z: nat ::
            ((x + y) * z) == ((x * z) + (y * z))
    ensures
        forall x: nat, y: nat, z: nat ::
            (x * (y - z)) == ((x * y) - (x * z))
    ensures
        forall x: nat, y: nat, z: nat ::
            ((x - y) * z) == ((x * z) - (y * z))
    ensures
        forall x: nat, y: nat, z: nat ::
            (x * (y + z)) == ((x * y) + (x * z))
    ensures
        forall x: nat, y: nat, z: nat ::
            ((x + y) * z) == ((x * z) + (y * z))
    ensures
        forall x: nat, y: nat, z: nat ::
            (x * (y - z)) == ((x * y) - (x * z))
    ensures
        forall x: nat, y: nat, z: nat ::
            ((x - y) * z) == ((x * z) - (y * z))
}