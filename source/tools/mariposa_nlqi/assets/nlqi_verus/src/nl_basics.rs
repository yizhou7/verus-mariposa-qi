use builtin_macros::*;
use builtin::*;
verus! {
pub closed spec fn eq_(x: int, y: int) -> bool;

pub closed spec fn add_(x: int, y: int) -> int;

pub closed spec fn sub_(x: int, y: int) -> int;

pub closed spec fn mul_(x: int, y: int) -> int;

pub closed spec fn mod_(x: int, y: int) -> int;

#[verifier::external_body]
pub proof fn lemma_mul_properties_auto_1()
ensures
	forall |x: int, y: int|
		eq_((add_(x, y)), (add_(y, x))),
	forall |x: int, y: int|
		eq_((mul_(x, y)), (mul_(y, x))),
	forall |x: int, y: int, z: int|
		eq_((mul_(x, (mul_(y, z)))), (mul_((mul_(x, y)), z))),
	forall |x: int, y: int, z: int|
		eq_((mul_(x, (add_(y, z)))), (add_((mul_(x, y)), (mul_(x, z))))),
	forall |x: int, y: int, z: int|
		eq_((mul_((add_(x, y)), z)), (add_((mul_(x, z)), (mul_(y, z))))),
	forall |x: int, y: int, z: int|
		eq_((mul_((sub_(y, z)), x)), (sub_((mul_(y, x)), (mul_(z, x))))),
	forall |x: int, y: int, z: int|
		eq_((mul_((sub_(x, y)), z)), (sub_((mul_(x, z)), (mul_(y, z))))),
	forall |x: int, y: int, m: int|
		eq_((mod_((mod_((mul_(x, y)), m)), m)), (mod_((mul_((mod_(x, m)), (mod_(y, m)))), m))),
	forall |x: int, y: int, m: int|
		eq_((mod_((mod_((mul_(x, y)), m)), m)), (mod_((mul_(x, (mod_(y, m)))), m))),
	forall |x: int, y: int, m: int|
		eq_((mod_((mod_((mul_(x, y)), m)), m)), (mod_((mul_(y, (mod_(x, m)))), m))),
	forall |x: int, y: int, m: int|
		eq_((mod_(x, m)), (mod_((add_(x, (mul_(y, m)))), m))),
	forall |x: int, y: int, m: int|
		eq_((mod_(x, m)), (mod_((add_((mul_(y, m)), x)), m))),
	forall |x: int, y: int, m: int|
		eq_((mod_(x, m)), (mod_((sub_(x, (mul_(y, m)))), m))),
	forall |x: int, y: int, m: int|
		eq_((mod_((add_(x, y)), m)), (mod_((add_((mod_(x, m)), (mod_(y, m)))), m))),
	forall |x: int, y: int, m: int|
		eq_((mod_((add_(x, y)), m)), (mod_((add_(x, (mod_(y, m)))), m))),
	forall |x: int, y: int, m: int|
		eq_((mod_((add_(x, y)), m)), (mod_((add_((mod_(x, m)), y)), m))),
	forall |x: int, y: int, m: int|
		eq_((mod_((sub_(x, y)), m)), (mod_((sub_((mod_(x, m)), (mod_(y, m)))), m))),
	forall |x: int, y: int, m: int|
		eq_((mod_((sub_(x, y)), m)), (mod_((sub_(x, (mod_(y, m)))), m))),
	forall |x: int, y: int, m: int|
		eq_((mod_((sub_(x, y)), m)), (mod_((sub_((mod_(x, m)), y)), m))),
	forall |x: int|
		eq_(x, x),
	forall |x: int, y: int|
		((eq_(x, y)) ==> eq_(y, x)),
	forall |x: int, y: int, z: int|
		((eq_(x, y) && eq_(y, z)) ==> eq_(x, z)),
	forall |x0: int, y0: int, x1: int, y1: int|
		((eq_(x0, x1) && eq_(y0, y1)) ==> eq_(add_(x0, y0), add_(x1, y1))),
	forall |x0: int, y0: int, x1: int, y1: int|
		((eq_(x0, x1) && eq_(y0, y1)) ==> eq_(sub_(x0, y0), sub_(x1, y1))),
	forall |x0: int, y0: int, x1: int, y1: int|
		((eq_(x0, x1) && eq_(y0, y1)) ==> eq_(mul_(x0, y0), mul_(x1, y1))),
	forall |x0: int, y0: int, x1: int, y1: int|
		((eq_(x0, x1) && eq_(y0, y1)) ==> eq_(mod_(x0, y0), mod_(x1, y1))),
{}

#[verifier::external_body]
pub proof fn lemma_add_comm(x: int, y: int)
ensures
	eq_((add_(x, y)), (add_(y, x))),
{}

#[verifier::external_body]
pub proof fn lemma_mul_comm(x: int, y: int)
ensures
	eq_((mul_(x, y)), (mul_(y, x))),
{}

#[verifier::external_body]
pub proof fn lemma_mul_assoc(x: int, y: int, z: int)
ensures
	eq_((mul_(x, (mul_(y, z)))), (mul_((mul_(x, y)), z))),
{}

#[verifier::external_body]
pub proof fn lemma_mul_dist(x: int, y: int, z: int)
ensures
	eq_((mul_(x, (add_(y, z)))), (add_((mul_(x, y)), (mul_(x, z))))),
	eq_((mul_((add_(x, y)), z)), (add_((mul_(x, z)), (mul_(y, z))))),
	eq_((mul_((sub_(y, z)), x)), (sub_((mul_(y, x)), (mul_(z, x))))),
	eq_((mul_((sub_(x, y)), z)), (sub_((mul_(x, z)), (mul_(y, z))))),
{}

#[verifier::external_body]
pub proof fn lemma_mod_mul_noop(x: int, y: int, m: int)
ensures
	eq_((mod_((mod_((mul_(x, y)), m)), m)), (mod_((mul_((mod_(x, m)), (mod_(y, m)))), m))),
	eq_((mod_((mod_((mul_(x, y)), m)), m)), (mod_((mul_(x, (mod_(y, m)))), m))),
	eq_((mod_((mod_((mul_(x, y)), m)), m)), (mod_((mul_(y, (mod_(x, m)))), m))),
{}

#[verifier::external_body]
pub proof fn lemma_mod_mul_vanish(x: int, y: int, m: int)
ensures
	eq_((mod_(x, m)), (mod_((add_(x, (mul_(y, m)))), m))),
	eq_((mod_(x, m)), (mod_((add_((mul_(y, m)), x)), m))),
	eq_((mod_(x, m)), (mod_((sub_(x, (mul_(y, m)))), m))),
{}

#[verifier::external_body]
pub proof fn lemma_mod_add_noop(x: int, y: int, m: int)
ensures
	eq_((mod_((add_(x, y)), m)), (mod_((add_((mod_(x, m)), (mod_(y, m)))), m))),
	eq_((mod_((add_(x, y)), m)), (mod_((add_(x, (mod_(y, m)))), m))),
	eq_((mod_((add_(x, y)), m)), (mod_((add_((mod_(x, m)), y)), m))),
{}

#[verifier::external_body]
pub proof fn lemma_mod_sub_noop(x: int, y: int, m: int)
ensures
	eq_((mod_((sub_(x, y)), m)), (mod_((sub_((mod_(x, m)), (mod_(y, m)))), m))),
	eq_((mod_((sub_(x, y)), m)), (mod_((sub_(x, (mod_(y, m)))), m))),
	eq_((mod_((sub_(x, y)), m)), (mod_((sub_((mod_(x, m)), y)), m))),
{}

}
