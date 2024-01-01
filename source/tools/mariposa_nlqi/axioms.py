from expression import *

class Equation:
    def __init__(self, left, right):
        self.left = left
        self.right = right
        
        lvs = self.left.get_vars() 
        rvs = self.right.get_vars()
        # if not lvs.issubset(rvs):
        #     print("WARNING: vars not subset")
        #     print(self.to_str(True))
        self.increasing_vars = rvs - lvs

    def to_str(self, uf=False):
        l = self.left.to_str(uf)
        r = self.right.to_str(uf)
        if not uf:
            return f"{l} == {r}"
        return f"eq_({l}, {r})"
    
    def left_applicable(self, e):
        assert isinstance(e, Expression)
        subs = self.left.get_substitution(e)
        return subs

    def right_applicable(self, e):
        assert isinstance(e, Expression)
        subs = self.right.get_substitution(e)
        return subs

    def try_apply(self, e):
        left = self.left_applicable(e)
        right = self.right_applicable(e)
        suffix = e.suffix

        increase = self.increasing_vars

        if left and right:
            if random.randint(0, 1) < 0.5:
                left = None
            else:
                right = None

        if left:
            return (self.right.apply_substitution(left, suffix, len(increase) != 0), left)
        if right:
            return (self.left.apply_substitution(right, suffix), right)

class LemmaCall:
    def __init__(self, name, args, uf):
        self.name = name
        self.args = args

        self.inst_call = "lemma_%s(%s)" % (self.name, ", ".join([a.to_str(uf) for a in self.args]))
        
        self.debug = "lemma_%s(%s)" % (self.name, ", ".join([a.to_str(False) for a in self.args]))
        self.auto_call = AUTO_CALL
        self.hint_call = None

    def set_hint(self, left, right):
        # print(left, right)
        self.hint_call = "assert (%s == %s)" % (left, right)

    def emit(self, mode):
        if mode == StepMode.AUTO or mode == StepMode.LBL:
            return self.auto_call

        if mode == StepMode.NLA:
            return ""

        if mode == StepMode.INST:
            return self.inst_call + ";\n" + self.hint_call 
        # + ";\n" + self.debug

        assert False

class Axiom:
    def __init__(self, name, vars, requires, ensures):
        self.name = name
        self.vars = vars
        self.requires = requires
        self.ensures = ensures

    def get_var_sig(self):
        return ", ".join([v.to_str() + ": Elem" for v in self.vars])

    def to_lemma_call(self, e, ne, subs, uf):
        args = [subs[v.value] for v in self.vars]
        call = LemmaCall(self.name, args, uf)
        call.set_hint(e.to_str(True), ne.to_str(True))
        return call

    def try_apply_lemma(self, e: Expression, uf):
        assert isinstance(e, Expression)

        if e.op == None:
            return None

        ress = []

        # debug = False
        # if e.to_str(True) == "(sub_((mul_(b0, a0)), (mul_(d0, c0))))":
        #     debug = True

        for ensure in self.ensures:
            res = ensure.try_apply(e)
            if res:
                # if debug:
                #     print(e.to_str(True))
                #     print("ensure", ensure.to_str(True))
                #     ne, subs = res
                #     for v in subs:
                #         print(v, ":" , subs[v].to_str(True))
                #     print(ne.to_str(True))
                #     print("")
                ress.append(res)

        if len(ress) == 0:
            return None
        (ne, subs) = random.choice(ress)

        call = self.to_lemma_call(e, ne, subs, uf)
        e.replace(ne)
        return call

    def to_str(self, uf=True):
        sig = f"pub proof fn lemma_{self.name}({self.get_var_sig()})"
        lines = ["#[verifier::external_body]", sig]

        if len(self.requires) != 0:
            lines += ["requires"] + ["\t" + r.to_str(uf) + "," for r in self.requires]
        assert len(self.ensures) != 0
        lines += ["ensures"] + ["\t" + r.to_str(uf) + "," for r in self.ensures] + ["{}"]
        return "\n".join(lines) + "\n"
    
    def get_quantified_clauses(self, uf):
        prelude = f"forall |{self.get_var_sig()}|"
        lines = []
        precond = " && ".join([r.to_str(uf) for r in self.requires])
        for r in self.ensures:
            if precond:
                clause = f"(({precond}) ==> {r.to_str(uf)})"
            else:
                clause = r.to_str(uf)
            lines += ["\t" + prelude, "\t\t" + clause + ","]
        return "\n".join(lines)

VX = Expression.var_init("x")
VY = Expression.var_init("y")
VZ = Expression.var_init("z")
VM = Expression.var_init("m")
# ZERO = Expression.const_init("zero()")
# ONE = Expression.const_init("one()")

def mk_add(x, y):
    return Expression(Operator.ADD, x, y, "")

def mk_sub(x, y):
    return Expression(Operator.SUB, x, y, "")

def mk_mul(x, y):
    return Expression(Operator.MUL, x, y, "")

def mk_mod_m(x):
    return Expression(Operator.MOD, x, VM, "")

def mk_eq(x, y):
    return Equation(x, y)

EQ_REF = Axiom("eq_ref",
        [VX],
        [],
        [mk_eq(VX, VX)])

EQ_SYM = Axiom("eq_sym",
        [VX, VY],
        [mk_eq(VX, VY)],
        [mk_eq(VY, VX)])

EQ_TRANS = Axiom("eq_trans",
        [VX, VY, VZ],
        [mk_eq(VX, VY), mk_eq(VY, VZ)],
        [mk_eq(VX, VZ)])

ADD_COMM = Axiom("add_comm",
        [VX, VY],
        [],
        [mk_eq(mk_add(VX, VY), mk_add(VY, VX))])

MUL_COMM = Axiom("mul_comm", 
        [VX, VY],
        [],
        [mk_eq(mk_mul(VX, VY), mk_mul(VY, VX))])

MUL_ASSOC = Axiom("mul_assoc", 
        [VX, VY, VZ],
        [],
        [mk_eq(
            mk_mul(VX, mk_mul(VY, VZ)), 
            mk_mul(mk_mul(VX, VY), VZ)
        )])

# ZERO_MUL = Axiom("zero_mul",
#        [VX],
#        [],
#        [mk_eq(mk_mul(VX, ZERO), ZERO)])          

# ZERO_ADD_SUB = Axiom("zero_add_sub",
#         [VX],
#         [],
#         [mk_eq(mk_add(VX, ZERO), VX),
#             mk_eq(mk_sub(VX, ZERO), VX),
#             mk_eq(mk_sub(VX, VX), ZERO)
#         ])

MUL_DIST = Axiom("mul_dist", 
        [VX, VY, VZ],
        [],
        [mk_eq(
            mk_mul(VX, mk_add(VY, VZ)),
            mk_add(mk_mul(VX, VY), mk_mul(VX, VZ))
        ),
        mk_eq(
            mk_mul(mk_add(VX, VY), VZ),
            mk_add(mk_mul(VX, VZ), mk_mul(VY, VZ))
        ),
        mk_eq(
            mk_mul(mk_sub(VY, VZ), VX),
            mk_sub(mk_mul(VY, VX), mk_mul(VZ, VX))
        ),
        mk_eq(
            mk_mul(mk_sub(VX, VY), VZ),
            mk_sub(mk_mul(VX, VZ), mk_mul(VY, VZ))
        )])

MOD_MUL_NOOP = Axiom("mod_mul_noop",
        [VX, VY, VM],
        [],
        [mk_eq(
            mk_mod_m(mk_mod_m(mk_mul(VX, VY))),
            mk_mod_m(mk_mul(mk_mod_m(VX), mk_mod_m(VY)))),
        mk_eq(
            mk_mod_m(mk_mod_m(mk_mul(VX, VY))),
            mk_mod_m(mk_mul(VX, mk_mod_m(VY)))),
        mk_eq(
            mk_mod_m(mk_mod_m(mk_mul(VX, VY))),
            mk_mod_m(mk_mul(VY, mk_mod_m(VX)))),
        ])

MOD_MUL_VANISH = Axiom("mod_mul_vanish",
        [VX, VY, VM],
        [],
        [mk_eq(
            mk_mod_m(VX),
            mk_mod_m(mk_add(VX, mk_mul(VY, VM)))),
        mk_eq(
            mk_mod_m(VX),
            mk_mod_m(mk_add(mk_mul(VY, VM), VX))),
        mk_eq(
            mk_mod_m(VX),
            mk_mod_m(mk_sub(VX, mk_mul(VY, VM)))),
        ])

MOD_ADD_NOOP = Axiom("mod_add_noop",
        [VX, VY, VM],
        [],
        [mk_eq(
            mk_mod_m(mk_add(VX, VY)),
            mk_mod_m(mk_add(mk_mod_m(VX), mk_mod_m(VY)))),
        mk_eq(
            mk_mod_m(mk_add(VX, VY)),
            mk_mod_m(mk_add(VX, mk_mod_m(VY)))),
        mk_eq(
            mk_mod_m(mk_add(VX, VY)),
            mk_mod_m(mk_add(mk_mod_m(VX), VY))),
        ])

MOD_SUB_NOOP = Axiom("mod_sub_noop",
        [VX, VY, VM],
        [],
        [mk_eq(
            mk_mod_m(mk_sub(VX, VY)),
            mk_mod_m(mk_sub(mk_mod_m(VX), mk_mod_m(VY)))),
        mk_eq(
            mk_mod_m(mk_sub(VX, VY)),
            mk_mod_m(mk_sub(VX, mk_mod_m(VY)))),
        mk_eq(
            mk_mod_m(mk_sub(VX, VY)),
            mk_mod_m(mk_sub(mk_mod_m(VX), VY))),
        ])

AXIOMS = [ADD_COMM, 
        MUL_COMM, MUL_ASSOC, MUL_DIST,
        # ZERO_MUL, ZERO_ADD_SUB,
        MOD_MUL_NOOP, MOD_MUL_VANISH, MOD_ADD_NOOP, MOD_SUB_NOOP]

def write_axioms():
    f = open("tools/mariposa_nlqi/assets/nlqi_verus/src/nl_basics.rs", "w+")
    f.write(
        """use builtin_macros::*;
use builtin::*;
verus! {
""")
    
    f.write("#[verifier::external_body]\n")
    f.write("pub struct Elem {x: int}\n\n")

    f.write("pub closed spec fn as_elem(x: int) -> Elem;\n\n")

    f.write("pub closed spec fn zero() -> Elem;\n\n")

    f.write("pub closed spec fn one() -> Elem;\n\n")

    f.write("pub closed spec fn eq_(x: Elem, y: Elem) -> bool;\n\n")

    # f.write("pub open spec fn eq_(x: Elem, y: Elem) -> bool\n")
    # f.write("{x == y}\n\n")

    for op in OP_PRETTY.keys():
        f.write(f"pub closed spec fn {op}(x: Elem, y: Elem) -> Elem;\n\n")

    # f.write("#[verifier(broadcast_forall)]\n")
    # f.write("pub proof fn lemma_eq_properties()\n")
    # f.write("ensures\n")
    # f.write("{}\n\n")

    f.write("#[verifier::external_body]\n")
    f.write("pub proof fn lemma_mul_properties_auto_1()\n")
    f.write("ensures\n")

    for a in AXIOMS:
        f.write(a.get_quantified_clauses(uf=True) + "\n")

    for a in [EQ_REF, EQ_SYM, EQ_TRANS]:
        f.write(a.get_quantified_clauses(uf=True) + "\n")

    for op in OP_PRETTY.keys():
        f.write("\tforall |x0: Elem, y0: Elem, x1: Elem, y1: Elem|\n")
        f.write(f"\t\t((eq_(x0, x1) && eq_(y0, y1)) ==> eq_({op}(x0, y0), {op}(x1, y1))),\n")

    f.write("{}\n\n")

    for a in AXIOMS:
        f.write(a.to_str(uf=True) + "\n")

    f.write("}\n")
#     print(a.to_str())

if __name__ == "__main__":
    write_axioms()
