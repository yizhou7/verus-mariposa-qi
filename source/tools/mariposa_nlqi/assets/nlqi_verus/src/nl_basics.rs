use builtin_macros::*;
use builtin::*;
verus! {
#[verifier::external_body]
pub struct Elem {x: int}

pub closed spec fn as_elem(x: int) -> Elem;

pub closed spec fn eq_(x: Elem, y: Elem) -> bool;

pub closed spec fn add_(x: Elem, y: Elem) -> Elem;

pub closed spec fn sub_(x: Elem, y: Elem) -> Elem;

pub closed spec fn mul_(x: Elem, y: Elem) -> Elem;

pub closed spec fn mod_(x: Elem, y: Elem) -> Elem;

#[verifier::external_body]
pub proof fn lemma_mul_properties_auto_1()
ensures
	forall |x: Elem, y: Elem|
		eq_((add_(x, y)), (add_(y, x))),
	forall |x: Elem, y: Elem|
		eq_((mul_(x, y)), (mul_(y, x))),
	forall |x: Elem, y: Elem, z: Elem|
		eq_((mul_(x, (mul_(y, z)))), (mul_((mul_(x, y)), z))),
	forall |x: Elem, y: Elem, z: Elem|
		eq_((mul_(x, (add_(y, z)))), (add_((mul_(x, y)), (mul_(x, z))))),
	forall |x: Elem, y: Elem, z: Elem|
		eq_((mul_((add_(x, y)), z)), (add_((mul_(x, z)), (mul_(y, z))))),
	forall |x: Elem, y: Elem, z: Elem|
		eq_((mul_((sub_(y, z)), x)), (sub_((mul_(y, x)), (mul_(z, x))))),
	forall |x: Elem, y: Elem, z: Elem|
		eq_((mul_((sub_(x, y)), z)), (sub_((mul_(x, z)), (mul_(y, z))))),
	forall |x: Elem, y: Elem, m: Elem|
		eq_((mod_((mod_((mul_(x, y)), m)), m)), (mod_((mul_((mod_(x, m)), (mod_(y, m)))), m))),
	forall |x: Elem, y: Elem, m: Elem|
		eq_((mod_((mod_((mul_(x, y)), m)), m)), (mod_((mul_(x, (mod_(y, m)))), m))),
	forall |x: Elem, y: Elem, m: Elem|
		eq_((mod_((mod_((mul_(x, y)), m)), m)), (mod_((mul_(y, (mod_(x, m)))), m))),
	forall |x: Elem, y: Elem, m: Elem|
		eq_((mod_(x, m)), (mod_((add_(x, (mul_(y, m)))), m))),
	forall |x: Elem, y: Elem, m: Elem|
		eq_((mod_(x, m)), (mod_((add_((mul_(y, m)), x)), m))),
	forall |x: Elem, y: Elem, m: Elem|
		eq_((mod_(x, m)), (mod_((sub_(x, (mul_(y, m)))), m))),
	forall |x: Elem, y: Elem, m: Elem|
		eq_((mod_((add_(x, y)), m)), (mod_((add_((mod_(x, m)), (mod_(y, m)))), m))),
	forall |x: Elem, y: Elem, m: Elem|
		eq_((mod_((add_(x, y)), m)), (mod_((add_(x, (mod_(y, m)))), m))),
	forall |x: Elem, y: Elem, m: Elem|
		eq_((mod_((add_(x, y)), m)), (mod_((add_((mod_(x, m)), y)), m))),
	forall |x: Elem, y: Elem, m: Elem|
		eq_((mod_((sub_(x, y)), m)), (mod_((sub_((mod_(x, m)), (mod_(y, m)))), m))),
	forall |x: Elem, y: Elem, m: Elem|
		eq_((mod_((sub_(x, y)), m)), (mod_((sub_(x, (mod_(y, m)))), m))),
	forall |x: Elem, y: Elem, m: Elem|
		eq_((mod_((sub_(x, y)), m)), (mod_((sub_((mod_(x, m)), y)), m))),
	forall |x: Elem|
		eq_(x, x),
	forall |x: Elem, y: Elem|
		((eq_(x, y)) ==> eq_(y, x)),
	forall |x: Elem, y: Elem, z: Elem|
		((eq_(x, y) && eq_(y, z)) ==> eq_(x, z)),
	forall |x0: Elem, y0: Elem, x1: Elem, y1: Elem|
		((eq_(x0, x1) && eq_(y0, y1)) ==> eq_(add_(x0, y0), add_(x1, y1))),
	forall |x0: Elem, y0: Elem, x1: Elem, y1: Elem|
		((eq_(x0, x1) && eq_(y0, y1)) ==> eq_(sub_(x0, y0), sub_(x1, y1))),
	forall |x0: Elem, y0: Elem, x1: Elem, y1: Elem|
		((eq_(x0, x1) && eq_(y0, y1)) ==> eq_(mul_(x0, y0), mul_(x1, y1))),
	forall |x0: Elem, y0: Elem, x1: Elem, y1: Elem|
		((eq_(x0, x1) && eq_(y0, y1)) ==> eq_(mod_(x0, y0), mod_(x1, y1))),
{}

#[verifier::external_body]
pub proof fn lemma_add_comm(x: Elem, y: Elem)
ensures
	eq_((add_(x, y)), (add_(y, x))),
{}

#[verifier::external_body]
pub proof fn lemma_mul_comm(x: Elem, y: Elem)
ensures
	eq_((mul_(x, y)), (mul_(y, x))),
{}

#[verifier::external_body]
pub proof fn lemma_mul_assoc(x: Elem, y: Elem, z: Elem)
ensures
	eq_((mul_(x, (mul_(y, z)))), (mul_((mul_(x, y)), z))),
{}

#[verifier::external_body]
pub proof fn lemma_mul_dist(x: Elem, y: Elem, z: Elem)
ensures
	eq_((mul_(x, (add_(y, z)))), (add_((mul_(x, y)), (mul_(x, z))))),
	eq_((mul_((add_(x, y)), z)), (add_((mul_(x, z)), (mul_(y, z))))),
	eq_((mul_((sub_(y, z)), x)), (sub_((mul_(y, x)), (mul_(z, x))))),
	eq_((mul_((sub_(x, y)), z)), (sub_((mul_(x, z)), (mul_(y, z))))),
{}

#[verifier::external_body]
pub proof fn lemma_mod_mul_noop(x: Elem, y: Elem, m: Elem)
ensures
	eq_((mod_((mod_((mul_(x, y)), m)), m)), (mod_((mul_((mod_(x, m)), (mod_(y, m)))), m))),
	eq_((mod_((mod_((mul_(x, y)), m)), m)), (mod_((mul_(x, (mod_(y, m)))), m))),
	eq_((mod_((mod_((mul_(x, y)), m)), m)), (mod_((mul_(y, (mod_(x, m)))), m))),
{}

#[verifier::external_body]
pub proof fn lemma_mod_mul_vanish(x: Elem, y: Elem, m: Elem)
ensures
	eq_((mod_(x, m)), (mod_((add_(x, (mul_(y, m)))), m))),
	eq_((mod_(x, m)), (mod_((add_((mul_(y, m)), x)), m))),
	eq_((mod_(x, m)), (mod_((sub_(x, (mul_(y, m)))), m))),
{}

#[verifier::external_body]
pub proof fn lemma_mod_add_noop(x: Elem, y: Elem, m: Elem)
ensures
	eq_((mod_((add_(x, y)), m)), (mod_((add_((mod_(x, m)), (mod_(y, m)))), m))),
	eq_((mod_((add_(x, y)), m)), (mod_((add_(x, (mod_(y, m)))), m))),
	eq_((mod_((add_(x, y)), m)), (mod_((add_((mod_(x, m)), y)), m))),
{}

#[verifier::external_body]
pub proof fn lemma_mod_sub_noop(x: Elem, y: Elem, m: Elem)
ensures
	eq_((mod_((sub_(x, y)), m)), (mod_((sub_((mod_(x, m)), (mod_(y, m)))), m))),
	eq_((mod_((sub_(x, y)), m)), (mod_((sub_(x, (mod_(y, m)))), m))),
	eq_((mod_((sub_(x, y)), m)), (mod_((sub_((mod_(x, m)), y)), m))),
{}

}
