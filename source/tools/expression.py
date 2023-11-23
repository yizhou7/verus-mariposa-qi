import random
import enum

random.seed(989312391)

VAR_PROB = 0.95
TERM_PROB = 0.1
VARS = ["a", "b", "c"]

def rconst():
    return int(random.random()*100)

class Operator(enum.Enum):
    ADD = "+"
    SUB = "-"
    MUL = "*"
    
    def new():
        r = random.random()
        if r <= OP_PROB[Operator.ADD]:
            return Operator.ADD
        elif r <= OP_PROB[Operator.ADD] + OP_PROB[Operator.SUB]:
            return Operator.SUB
        else:
            return Operator.MUL

OP_PROB = {
    Operator.ADD: 0.1,
    Operator.SUB: 0.1,
    Operator.MUL: 0.8,
}

class Mode(enum.Enum):
    INST_HINT = "inst_hint"
    INST_ONLY = "inst_only"
    AUTO_HINT = "auto_hint"
    AUTO_ONLY = "auto_only"
    NL_HINT = "nl_arith_hint"
    NL_ONLY = "nl_arith_only"

class LemmaCall:
    def __init__(self, name, args):
        self.name = name
        self.args = args
        
        self.inst_call = "lemma_%s(%s);" % (self.name, ", ".join([str(a) for a in self.args]))
        self.auto_call = "lemma_%s_auto();" % self.name
        self.hint_call = None

    def set_hint(self, left, right):
        self.hint_call = "assert(%s == %s);" % (left, right)

    def emit(self, mode):
        if mode == Mode.AUTO_ONLY: 
            return self.auto_call

        if mode == Mode.NL_ONLY:
            return ""

        if mode == Mode.INST_ONLY:
            return self.inst_call

        if mode == Mode.INST_HINT:
            return self.inst_call + " " + self.hint_call

        assert self.hint_call != None

        if mode == Mode.AUTO_HINT:
            return self.auto_call + " " + self.hint_call
        
        if mode == Mode.NL_HINT:
            return self.hint_call

        assert False

class Expression:
    def __init__(self, op, left, right):
        self.op = op

        if op == None:
            if random.random() <= VAR_PROB:
                self.value = random.choice(VARS)
            else:
                self.value = rconst()
        else:
            self.value = None

        self.left = left
        self.right = right

    @classmethod
    def random_init(cls, op_count, depth):
        op = Operator.new()
        if random.random() < TERM_PROB or depth == 0 or op_count == 0:
            left, right, op = None, None, None
        else:
            left = Expression.random_init(op_count-1, depth-1)
            right = Expression.random_init(op_count-1, depth-1)
        return cls(op, left, right)

    def list_op_nodes(self):
        if self.op == None:
            return []
        else:
            return [self] + self.left.list_op_nodes() + self.right.list_op_nodes()

    def associative_rewrite(self):
        call = None

        if self.op != Operator.MUL:
            return call

        left_enable = self.left.op == self.op
        right_enable = self.right.op == self.op

        if left_enable and right_enable:
            # if both left and right can be rewritten, randomly choose one
            if random.random() < 0.5:
                left_enable = False

        orig = str(self)

        if left_enable:
            call = LemmaCall("mul_is_associative", [self.left.left, self.left.right, self.right])
            tmp_left = self.left
            self.left = tmp_left.left
            self.right = Expression(self.op, tmp_left.right, self.right)
            call.set_hint(orig, str(self))

        if right_enable:
            call = LemmaCall("mul_is_associative", [self.left, self.right.left, self.right.right])
            tmp_right = self.right
            self.right = tmp_right.right
            self.left = Expression(self.op, self.left, tmp_right.left)
            call.set_hint(orig, str(self))

        return call
    
    def commutative_rewrite(self):
        if self.op != Operator.MUL:
            return None
        orig = str(self)
        call = LemmaCall("mul_is_commutative", [self.left, self.right])
        self.left, self.right = self.right, self.left
        call.set_hint(orig, str(self))
        return call
    
    def mul_add_distributive_rewrite(self):
        call = None

        if self.op != Operator.MUL:
            return call

        left_enable = self.left.op == Operator.ADD
        right_enable = self.right.op == Operator.ADD
        
        if left_enable and right_enable:
            # if both left and right can be rewritten, randomly choose one
            if random.random() < 0.5:
                left_enable = False

        orig = str(self)

        if left_enable:
            call =  LemmaCall("mul_add_is_distributive", [self.left.left, self.left.right, self.right])
            tmp_left = self.left
            self.left = Expression(Operator.MUL, tmp_left.left, self.right)
            self.right = Expression(Operator.MUL, tmp_left.right, self.right)
            self.op = Operator.ADD
            call.set_hint(orig, str(self))

        if right_enable:
            call =  LemmaCall("mul_add_is_distributive", [self.left, self.right.left, self.right.right])
            tmp_right = self.right
            self.right = Expression(Operator.MUL, tmp_right.left, self.left)
            self.left = Expression(Operator.MUL, tmp_right.right, self.left)
            self.op = Operator.ADD
            call.set_hint(orig, str(self))

        return call

    def mul_sub_distributive_rewrite(self):
        call = None

        if self.op != Operator.MUL:
            return call

        left_enable = self.left.op == Operator.SUB
        right_enable = self.right.op == Operator.SUB
        
        if left_enable and right_enable:
            # if both left and right can be rewritten, randomly choose one
            if random.random() < 0.5:
                left_enable = False

        orig = str(self)

        if left_enable:
            call =  LemmaCall("mul_sub_is_distributive", [self.left.left, self.left.right, self.right])
            tmp_left = self.left
            self.left = Expression(Operator.MUL, tmp_left.left, self.right)
            self.right = Expression(Operator.MUL, tmp_left.right, self.right)
            self.op = Operator.SUB
            call.set_hint(orig, str(self))

        if right_enable:
            call =  LemmaCall("mul_sub_is_distributive", [self.left, self.right.left, self.right.right])
            tmp_right = self.right
            self.right = Expression(Operator.MUL, tmp_right.left, self.left)
            self.left = Expression(Operator.MUL, tmp_right.right, self.left)
            self.op = Operator.SUB
            call.set_hint(orig, str(self))

        return call

    def __str__(self):
        if self.op == None:
            return str(self.value)
        return "(%s%s%s)" % (self.left, self.op.value, self.right)

funs = [lambda e: e.associative_rewrite(), 
        lambda e: e.commutative_rewrite(), 
        lambda e: e.mul_add_distributive_rewrite(),
        lambda e: e.mul_sub_distributive_rewrite()]

class CalcEmitter:
    def __init__(self, op_count, max_depth):
        self.e = Expression.random_init(op_count, max_depth)
        self.steps = []

        for _ in range(10):
            cur = str(self.e)
            nodes = self.e.list_op_nodes()
            random.shuffle(nodes)

            for n in nodes:
                fun = random.choice(funs)
                call = fun(n)
                if call != None:
                    self.steps.append((cur, call))
                    # print("\t\t{" + str(call) + "}")
                    break
        self.last = str(self.e)

    def emit(self, mode):
        args = ",".join([v + ": int" for v in VARS])
        sig = f"pub proof fn calc_algebra_{mode.value}({args})"
        if mode == Mode.NL_ONLY or mode == Mode.NL_HINT:
            sig += " by (nonlinear_arith)"
        else:
            sig = " #[verifier::spinoff_prover]\n" + sig
        print(sig)
        print("{")
        print("\tcalc !{")
        print("\t\t(==)")
        for s in self.steps:
            print("\t\t" + s[0] + ";")
            print("\t\t\t{" + s[1].emit(mode) + "}")
        print("\t\t" + str(self.last) + ";")
        print("\t}")
        print("}")
        print("")

em = CalcEmitter(5, 3)

print("""use builtin_macros::*;
use builtin::*;
use vstd::calc_macro::*;
mod nl_basics;
use nl_basics::*;

verus! {""")

for m in Mode:
    em.emit(m)

print("""fn main() {
}

} // verus!""")