module nl_basics {

    lemma lemma_mul_is_associative(x: int, y: int, z: int)
        ensures
            (x * (y * z)) == ((x * y) * z)

    lemma lemma_mul_is_commutative(x: int, y: int)
        ensures
            (x * y) == (y * x)

    lemma lemma_mul_is_distributive(x: int, y: int, z: int)
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
        forall x: int, y: int ::
            (x * y) == (y * x)
    ensures
        forall x: int, y: int, z: int ::
            (x * (y * z)) == ((x * y) * z)
    ensures
        forall x: int, y: int, z: int ::
            (x * (y * z)) == ((x * y) * z)
    ensures
        forall x: int, y: int, z: int ::
            (x * (y + z)) == ((x * y) + (x * z))
    ensures
        forall x: int, y: int, z: int ::
            ((x + y) * z) == ((x * z) + (y * z))
    ensures
        forall x: int, y: int, z: int ::
            (x * (y - z)) == ((x * y) - (x * z))
    ensures
        forall x: int, y: int, z: int ::
            ((x - y) * z) == ((x * z) - (y * z))
    ensures
        forall x: int, y: int, z: int ::
            (x * (y + z)) == ((x * y) + (x * z))
    ensures
        forall x: int, y: int, z: int ::
            ((x + y) * z) == ((x * z) + (y * z))
    ensures
        forall x: int, y: int, z: int ::
            (x * (y - z)) == ((x * y) - (x * z))
    ensures
        forall x: int, y: int, z: int ::
            ((x - y) * z) == ((x * z) - (y * z))
}